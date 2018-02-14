let cytoscape = require('./vendor/cytoscape');
let graph = require('./lib/graph');
let domtoimage = require('./vendor/dom-to-image');
let colors = require('./lib/colors')();

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


  if (!window.cy) {
    window.cy = document.createElement("div");
    cy.setAttribute('id','cy');
    document.body.appendChild(cy);
  }

  window.cy_graphs = _.object(_.map(cyd_graphs, ({info,elements}) => {
    let id = info.id;
    let div = document.createElement("div")
    div.setAttribute('id',id);
    div.classList.add('innerGraph');
    cy.appendChild(div);
    //document.body.appendChild(div);
    let g = cytoscape({
      id: id,
      container: div,
      elements: elements,
      style: [
        {
          selector: 'node',
          style: {
            'label': 'data(label)',
            'text-halign': 'center',
            'text-valign': 'center'
          }
        },
        {
          selector: 'node[highlight]',
          style: {
            'background-color': e => colors.get(e.data("highlight")),
          }
        },
        {
          selector: 'edge',
          style: {
            //'opacity': 0.6,
            'source-label': 'data(taillabel)',
            'target-label': 'data(headlabel)',
            'curve-style': 'bezier',
            'source-text-offset': '0.5em',
            'target-text-offset': '0.5em'
          }
        }
      ],
      layout: { name: 'cose-bilkent', animate: false},
      userZoomingEnabled: false,
    });


    //g.center();

    return [id,g];
  }));


  window.cy_basis = cytoscape({
    container: cy,
    elements:cyd_basis.elements,
    autoungrabify: true,
    autounselectify: true,
    maxZoom: 1.8,
    minZoom: 0.1,

    style: [ // the stylesheet for the graph
      {
        selector: 'node',
        style: {
          'background-color': '#666',
          'background-opacity': 0,
          'border-width': '2px',
          'border-style': 'solid',
          'border-color': 'black',
          'border-opacity': '0.1',
          'label': 'data(id)',
          'width': '200px',
          'height': '200px',
          'font-size': '28px',
          'label': 'data(label)',
        }
      },
      {
        selector: 'node.activeCC, node.activeCCLong',
        style: {
          'background-color': '#2ba7ef',
          'background-opacity': 0.1,
        }
      },
      {
        selector: 'node.activeCC',
        style: {
          'border-opacity': 1
        }
      },
      {
        selector: 'node.hover',
        style: {
          //'border-color': '#0654d3',
          'background-color': '#0654d3',
          //'border-width': '10px',
          'background-opacity': 0.3,
          'border-opacity': 1
        }
      },
      {
        selector: 'edge',
        style: {
          //'source-label': 'data(sourceLabel)',
          //'target-label': 'data(targetLabel)',
          'width': 2,
          'line-color': '#1a8416',
          'line-style': 'solid',
          'opacity': '0.7',
          'target-arrow-color': '#ccc',
          'target-arrow-shape': 'triangle',
          //'source-endpoint': 'outside-to-node',
          //'target-endpoint': 'outside-to-line',
          'curve-style': 'unbundled-bezier'
        }
      },

      {
        selector: "edge[conflict]",
        style: {
          'line-style': 'dashed',
          'width': 1,
          'line-color': '#A0A0A0',
          'visibility': 'hidden'
          //'curve-style': 'unbundled-bezier'
        }

      },
      {
        selector: "edge[conflict].activeCC.visible, edge[conflict].activeCCLong.visible",
        style: {
          'visibility': 'visible'
        }
      },
      {
        selector: 'edge[^conflict].hover',
        style: {
          opacity: 0.9,
          width: 7,
          color: '#27db20'
        }
      },
      {
        selector: 'edge[conflict].hover',
        style: {
          opacity: 0.9,
          width: 7,
          color: '#505050'
        }
      },
      {
        selector: 'edge.activeCC, edge.activeCCLong',
        style: {
          opacity: 0.8,
          width: 7,
        }
      },
      {
        selector: 'edge.activeCC',
        style: {
          opacity: 1,
          color: '#0e540b',
          width: 7,
        }
      },
      {
        selector: 'edge[conflict].activeCC, edge[conflict].activeCCLong',
        style: {
          'line-color': '#808080',
          width: 7,
        }
      },
      {
        selector: 'edge[conflict].activeCC',
        style: {
          'line-color': '#404040',
          width: 7,
        }
      },

    ],


  });

  let dagre_data = { name: 'dagre',
    spacingFactor: 1.5,
    padding: 60,
    transform: (node,position) => { return {x: position.x, y: node.cy().height()-position.y} }

  };

  let conflict_data = dagre_data;

  cy_basis.collection('[^conflict]').layout(dagre_data).run();

  let conflicts = cy_basis.collection('[conflict]');

  if (getConflict() === null || getConflict() === "true") {
    setConflict(conflicts,true);
  }

  conflicts.layout(conflict_data).run();

  cy_basis.collection('edge').on('mouseover', evt => evt.target.addClass('hover'));

  cy_basis.collection('edge').on('mouseout', evt => evt.target.removeClass('hover'));

  let activationZone = node => {
    let c = node
    c = c.union(node.neighborhood('edge[conflict]'));
    c = c.union(graph.filteredSuccessors(node, '[^conflict]'));
    return c.union(graph.filteredPredecessors(node, '[^conflict]'));
  }

  let actives = cy_basis.collection();

  cy_basis.collection('node').on('mouseover', evt => {
    evt.target.addClass('hover');
    activationZone(evt.target).addClass('activeCC');
  });

  cy_basis.collection('node').on('mouseout', evt => {
    evt.target.removeClass('hover');
    activationZone(evt.target).removeClass('activeCC');
  });

  cy_basis.collection('node').on('tap', evt => {
    actives.removeClass('activeCCLong');
    actives = activationZone(evt.target);
    actives.addClass('activeCCLong');
  });

  cy_basis.on('tap', evt => {
    if (evt.target == cy_basis) {
      actives.removeClass('activeCCLong');
      actives = cy_basis.collection();
    }
  });


  adjust = (zoom) => {
    let wHeight = window.innerHeight;
    let wWidth = window.innerWidth;

    _.each(cy_graphs, (g,id) => {

      let host_node = cy_basis.nodes('#'+id);
      if (host_node.length == 0) {
        return;
      }
      let pos = host_node.renderedPosition(),
      w = host_node.renderedWidth(),
      h = host_node.renderedHeight();

      // We don't use is_contained for now because it uses the positions
      // *before* the zoom; so we are left with dangling midpoints on the
      // side of the screen. FIXME
      if (true || is_contained(wHeight,wWidth,pos.x,pos.y,w,h)) {

        //ccy.zoom({level:cy.zoom(),renderedPosition:{x:pos.x-w/2, y:pos.y-h/2}});
        g.container().style.left = pos.x - w/2;
        g.container().style.top = pos.y - h/2;
        g.container().style.width = w;
        g.container().style.height = h;

        if (zoom) {
          // Somehow doing resize() before fit() makes everything faster (fit() alone is slow)
          g.resize();
          g.center();
          g.fit(0.05*w);
          // Old method to rezoom fast was
          //  g.zoom({level:cy_basis.zoom(),renderedPosition:{x:0,y:0}}); // fast
          //  imperfect but this was incorrect: this assumed the initial zoom level
          //  (to fit the default 200px * 200px box for inner graphs) was 1. So if
          //  I go this route again, I need to store, for each inner graph g, their
          //  initial zoom level z_g and then if cy_basis has zoom level z, I give
          //  g the zoom level z * z_g.
        }
      }
    });
  };

  cy_basis.on('pan', () => {
    adjust(false);
  });

  cy_basis.on('zoom', () =>  {
    adjust(true);
  });

  adjust(true);
};

document.addEventListener('keypress', e => {
  if (e.key === 'c') {
    toggleConflict(cy_basis.collection('[conflict]'));
  }
  if (e.key === 'r') {
    cy_basis.fit();
  }
  if (e.key === 'p') {
    let node = window.cy;
    let screenlink = document.getElementById('screenlink');

    domtoimage.toPng(node)
    .then(dataUrl => {
      screenlink.classList.add('ready');
      screenlink.href = dataUrl;
      screenlink.click();
    })
  .catch(error => {
    console.error('oops, something went wrong!', error);
  });
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
