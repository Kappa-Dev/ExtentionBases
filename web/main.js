let cytoscape = require('./vendor/cytoscape');
let graph = require('./lib/graph');
let colors = require('./lib/colors')();
let styles = require('./lib/styles');

let WS = require('./lib/ws-client');

let perfNum = 0;
let perf = (a) => {
  let t0  = 0;
  let pnum = 0;
  const start = a => {
    t0 = performance.now();
    pnum = a ? a : perfNum++;
    console.log(`Start timing #${pnum}`);
  };
  const end = () => {
    let t1 = performance.now();
    console.log(`End timing #${pnum}: ${Math.round((t1-t0))}ms.`);
  };
  start(a);
  return {
    end,
    next: (a) => {end(); start(a);}
  }
}


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

let getHideMaps = () => localStorage.getItem('hide_maps')
let setHideMaps = (col,b) => {
  col.toggleClass('defaultHide',b),
  localStorage.setItem('hide_maps',b);
}
let toggleHideMaps = col => setHideMaps(col, getHideMaps() === "false")

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

  let p0 = perf();
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

  p0.end();

  let p1 = perf();


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
    style: styles
  });

  p1.end();
  let p2 = perf();



  // Layout templates
  let dagre_data = { name: 'dagre',
    spacingFactor: 1.5,
    padding: 60,
    transform: (node,position) => { return {x: position.x, y: node.cy().height()-position.y} }
  };
  let conflict_data = dagre_data;
  p2.next('outers');

  // Subsets of the full graph
  let outers = cy_basis.filter('[outer][^conflict]');
  let conflicts = cy_basis.filter('[outer][conflict]');
  p2.next('inners');
  let inners = _.object(_.map(cyd_graphs, ({info}) => {
    return [info.id, cy_basis.collection()]
  }));
  cy_basis.filter('[^outer]').forEach( e => {
    let id = e.data().fromGraph;
    inners[id].merge(e);
  });

  p2.end();

  let p3 = perf();


  // Run each layout separately
  outers.layout(dagre_data).run();
  p3.end();
  let p4 = perf();
  conflicts.layout(conflict_data).run();
  p4.end();

  let p5 = perf();

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

  p5.end();

  let p6 = perf();

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

  p6.end();
  let p7 = perf();

  //window.inners = inners;

  let edgeLength = e => {
    //console.log("edge", e.data().source, e.data().target);
    //console.log(e.sourceEndpoint(),e.targetEndpoint());
    let sPos = e.sourceEndpoint();
    let tPos = e.targetEndpoint();
    return Math.sqrt(Math.pow(sPos.x - tPos.x,2) + Math.pow(sPos.y - tPos.y,2));
  }

  p7.end();
  let p8 = perf();


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
    let callbacks = [];
    let px = perf('x');
    _.each(inners, (inner,id) => {
      //console.log("ID ", id);
      let nodes = inner.filter(e => !e.data().source);
      let edges = inner.filter(e => e.data().source);
      let num = nodes.size() < 10 ? 0 : nodes.size() - 10;
      num = nodes.size();
      let factorFont = linearCutoff(1,5,1,20,num);
      //console.log(nodes.size(),factorFont);

        _.each(nodes, (n,k) => {

          callbacks.push(() => {
            n.data('fontSize',(initMainFont/factorFont)+'px');
            n.addClass('localnode');
          });

        });
        _.each(edges, (e,k) => {
          let length = edgeLength(e);
          let factor = linearCutoff(2,1,1,20,length);
          //console.log("length: ",length,", factor: ", factor);
          callbacks.push(() => {
            //e.style('font-size','5px');
            e.data('fontSize',(initEdgeFont/factor)+'px');
            e.data('sourceTextOffset', (initOffset/(factor*1.5))+'px');
            e.data('targetTextOffset', (initOffset/(factor*1.5))+'px');
            e.addClass('localedge');
          });
        });
      });
     px.end();
    cy_basis.startBatch();
    let py = perf('cb');
    _.each(callbacks, f => { f(); })
    py.end();
    cy_basis.endBatch();
  }
  adjust();

  p8.end();
  let p9 = perf();


  // show conflicts or not
  if (getConflict() === null || getConflict() === "true") {
    setConflict(conflicts,true);
  }

  if (getHideMaps() === null || getHideMaps() === "false") {
    setHideMaps(cy_basis.filter('[outer][^conflict]'),false);
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

  let actives = cy_basis.filter('*'); // full collection

  window.getHoverLongs = () => { return cy_basis.filter('node.hoverLong')} ;

  window.updateActives = () => {
    let hoverLongs = getHoverLongs();
    cy_basis.batch( () => {
      actives.removeClass('activeCCLong');
      if (hoverLongs.empty()) {
        actives = cy_basis.collection(); // empty collection
      } else {
        actives = cy_basis.filter('*');
        hoverLongs.forEach( e => {
          actives = actives.intersection(activationZone(e))
        });
      }
      actives.addClass('activeCCLong');
    });
  };


  cy_basis.filter('node[outer]').on('mouseover', evt => {
    evt.target.addClass('hover');
    activationZone(evt.target).addClass('activeCC');
  });

  cy_basis.filter('node[outer]').on('mouseout', evt => {
    evt.target.removeClass('hover');
    activationZone(evt.target).removeClass('activeCC');
  });

  cy_basis.filter('node[outer]').on('tap', evt => {
    evt.target.toggleClass('hoverLong');
    updateActives();
  });

  p9.end();

};

document.addEventListener('keypress', e => {
  if (e.key === 'x') {
    getHoverLongs().removeClass('hoverLong');
    updateActives();
  }
  if (e.key === 'c') {
    toggleConflict(cy_basis.filter('[conflict]'));
  }
  if (e.key === 'r') {
    cy_basis.fit();
  }
  if (e.key === 'm') {
    toggleHideMaps(cy_basis.filter('[outer][^conflict]'));
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
