let cytoscape = require('./vendor/cytoscape');
let graph = require('./lib/graph');
let colors = require('./lib/colors')();
let styles = require('./lib/styles');

let WS = require('./lib/ws-client');


let clear = () => {
  if (window.cy_graphs) {
    _.each(cy_graphs, g => g.destroy());
  }
  if (window.cy_basis) {
    cy_basis.destroy();
  }
}


let getConflict = () => localStorage.getItem('show_conflict')
let setConflict = (col,b) => {
  col.toggleClass('visible',b);
  localStorage.setItem('show_conflict',b);
}
let toggleConflict = col => setConflict(col, getConflict() === "false")

// websocket callback
let websocket_callback = (type,content) => {

  if (type == "log") {
    console.log("Received from server: "+content);
  } else if (type == "graph") {
    console.log("Received graph from server");
    //console.log(content);

    let gls = graphlibDot.readMany(content);

    let gl_basis = gls.shift();
    let gl_graphs = gls;

    let cyd_basis = graph.gl_to_cy_data(gl_basis);
    let cyd_graphs = _.map(gl_graphs,graph.gl_to_cy_data);

    init(cyd_basis, cyd_graphs);
  } else {
    console.log("Unknown message type: "+type+". Content: "+content);
  }
}



let ws_client = WS({url: 'ws://localhost:3001', cb: websocket_callback});

ws_client.connect();

cytoscape.use(require('./vendor/cytoscape-dagre'));
cytoscape.use(require('./vendor/cytoscape-cose-bilkent'));

let init = (cyd_basis,cyd_graphs) => {
  clear();

  // Attach metadata to basis elements (outer) and midpoint elements (inner)
  _.each(cyd_basis.elements, g => { g.data.outer = true; });
  _.each(cyd_graphs, ({info,elements}) => {
    _.each(elements, g => {
      g.data.inner = true;
      g.data.fromGraph = info.id;
      if (g.data.id) g.data.id = `${info.id}/${g.data.id}`;
      if (g.data.source) g.data.source = `${info.id}/${g.data.source}`;
      if (g.data.target) g.data.target = `${info.id}/${g.data.target}`;
    });
  });


  // Setup full graph

  if (!window.cy) {
    window.cy = document.createElement("div");
    cy.setAttribute('id','cy');
    document.body.appendChild(cy);
  }

  window.cy_basis = cytoscape({
    container: cy,
    elements:cyd_basis.elements.concat(..._.map(cyd_graphs, ({elements}) => elements)),
    autoungrabify: true,
    autounselectify: true,
    maxZoom: 5,
    minZoom: 0.01,
    style: styles ,
  });



  // Layout templates
  let dagre_data = { name: 'dagre',
    spacingFactor: 1.5,
    padding: 60,
    transform: (node,position) => { return {x: position.x, y: node.cy().height()-position.y} }
  };
  let conflict_data = dagre_data;

  // Subsets of the full graph
  let outers = cy_basis.filter('[outer][^conflict]');
  let conflicts = cy_basis.filter('[outer][conflict]');
  let inners = _.object(_.map(cyd_graphs, ({info}) => {
    const inner = cy_basis.filter(e => e.data().fromGraph == info.id);
    return [info.id, inner];
  }));


  // Run each layout separately
  outers.layout(dagre_data).run();
  conflicts.layout(conflict_data).run();

  // Adapt inner_nodes size to inner graph size
  _.each(inners, (inner,id) => {
    //console.log("ID ", id);
    let init = 30;
    let nodes = inner.filter(e => !e.data().source);
    let base = 3;
    let num = nodes.size() < 10 ? 0 : nodes.size() - 10;
    num = nodes.size();
    let factor = Math.log10(num+base)/Math.log10(base);
    //console.log(nodes.size(),factorFont);
    _.each(nodes, (n,k) => {
      n.style('width',init/factor);
      n.style('height',init/factor);
    });
  });



  let paddingPc = 0.05;
  _.each(inners, (inner,id) => {
    const outer = cy_basis.getElementById(id);
    const pos = outer.position();
    const w = outer.width();
    const h = outer.height();
    inner.layout({
      name: 'cose-bilkent',
      animate: 'end', // end?
      boundingBox: {
        x1: pos.x - w/2 + paddingPc*w,
        y1: pos.y - h/2 + paddingPc*h,
        w: w - paddingPc*w*2,
        h: h - paddingPc*h*2
      }
    }).run()
  });

  //window.inners = inners;

  let edgeLength = e => {
    //console.log("edge", e.data().source, e.data().target);
    //console.log(e.sourceEndpoint(),e.targetEndpoint());
    let sPos = e.sourceEndpoint();
    let tPos = e.targetEndpoint();
    return Math.sqrt(Math.pow(sPos.x - tPos.x,2) + Math.pow(sPos.y - tPos.y,2));
  }

  //window.edgeLength = edgeLength;

  let linearCutoff = (start, end, from, to, i) => {
    if (i <= from) return start;
    if (i >= to) return end;
    return start + (((i-from)/(to-from))*(end-start));
  }

  // Adapt inner nodes fonts and edges size to inner graph size
  let adjust = () => {
    let initFont = 12;
    let initEdgeFont = 4;
    let initOffset = 5;
    let initMainFont = 14;
    _.each(inners, (inner,id) => {
      //console.log("ID ", id);
      let nodes = inner.filter(e => !e.data().source);
      let edges = inner.filter(e => e.data().source);
      let num = nodes.size() < 10 ? 0 : nodes.size() - 10;
      num = nodes.size();
      let factorFont = linearCutoff(1,5,1,20,num);
      //console.log(nodes.size(),factorFont);
      _.each(nodes, (n,k) => {
        n.style('font-size',(initMainFont/factorFont)+'px');
      });
      _.each(edges, (e,k) => {
        let length = edgeLength(e);
        let factor = linearCutoff(2,1,1,20,length);
        //console.log("length: ",length,", factor: ", factor);
        e.style('font-size',(initEdgeFont/factor)+'px');
        //e.style('font-size','5px');
        e.style('source-text-offset', (initOffset/(factor*1.5))+'px');
        e.style('target-text-offset', (initOffset/(factor*1.5))+'px');
      });
    });
  }
  adjust();


  // show conflicts or not
  if (getConflict() === null || getConflict() === "true") {
    setConflict(conflicts,true);
  }

  // Interactivity
  cy_basis.filter('edge[outer]').on('mouseover', evt => evt.target.addClass('hover'));

  cy_basis.filter('edge[outer]').on('mouseout', evt => evt.target.removeClass('hover'));

  let activationZone = node => {
    let c = node
    c = c.union(node.neighborhood('edge[conflict]'));
    c = c.union(graph.filteredSuccessors(node, '[^conflict]'));
    return c.union(graph.filteredPredecessors(node, '[^conflict]'));
  }

  let actives = cy_basis.collection();

  cy_basis.filter('node[outer]').on('mouseover', evt => {
    evt.target.addClass('hover');
    activationZone(evt.target).addClass('activeCC');
  });

  cy_basis.filter('node[outer]').on('mouseout', evt => {
    evt.target.removeClass('hover');
    activationZone(evt.target).removeClass('activeCC');
  });

  cy_basis.filter('node[outer]').on('tap', evt => {
    actives.removeClass('activeCCLong');
    actives.removeClass('hoverLong');
    actives = activationZone(evt.target);
    actives.addClass('activeCCLong');
    evt.target.addClass('hoverLong');
  });

  cy_basis.on('tap', evt => {
    if (evt.target == cy_basis) {
      actives.removeClass('activeCCLong');
      actives.removeClass('hoverLong');
      actives = cy_basis.collection();
    }
  });
};

document.addEventListener('keypress', e => {
  if (e.key === 'c') {
    toggleConflict(cy_basis.filter('[conflict]'));
  }
  if (e.key === 'r') {
    cy_basis.fit();
  }
  if (e.key === 'p') {
    let screenlink = document.getElementById('screenlink');

    let dataUrl = cy_basis.png({full:true,bg: "white"});
    screenlink.classList.add('ready');
    screenlink.href = dataUrl;
    screenlink.click();
  }
});


document.addEventListener("DOMContentLoaded", function(event) {
  let help = document.getElementsByClassName('help')[0];
  help.addEventListener('mouseenter', e => help.classList.remove('idle'));
  help.addEventListener('mouseleave', e => help.classList.add('idle'));
});


// Performance links for later:
// https://github.com/cytoscape/cytoscape.js/blob/master/documentation/md/performance.md
// https://github.com/cytoscape/cytoscape.js/issues/292
// Idea for later performance: detect for each if
