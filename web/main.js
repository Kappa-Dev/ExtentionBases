let cytoscape = require('./vendor/cytoscape');
let graph = require('./lib/graph');
let WS = require('./lib/ws-client');

let clear = () => {
  if (window.cy_graphs) {
    _.each(cy_graphs, g => g.destroy());
  }
  if (window.cy_basis) {
    cy_basis.destroy();
  }
}

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


  window.cy = document.createElement("div");
  cy.setAttribute('id','cy');
  document.body.appendChild(cy);

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
          'label': 'data(id)',
          'text-halign': 'center',
          'text-valign': 'center'
          }
        },
        {
        selector: 'edge',
        style: {
          'source-label': 'data(taillabel)',
          'target-label': 'data(headlabel)',
          'curve-style': 'bezier',
          'source-text-offset': '0.5em',
          'target-text-offset': '0.5em'
        }
        }
      ],
      layout: { name: 'cose-bilkent'},
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
        selector: 'edge',
        style: {
          'source-label': 'data(sourceLabel)',
          'target-label': 'data(targetLabel)',
          'width': 2,
          'line-color': '#1a8416',
          'line-style': 'dashed',
          //'line-opacity': '0.2',
          'target-arrow-color': '#ccc',
          'target-arrow-shape': 'triangle',
          //'source-endpoint': 'outside-to-node',
          //'target-endpoint': 'outside-to-line',
          'curve-style': 'unbundled-bezier'
        }
      },
      {
        selector: 'edge.hover',
        style: {
          width: 5,
          'line-style': 'solid'
        }
      }
      ],


      layout: {
        name: 'breadthfirst',
        //roots: ['arc'],
        directed: true,
        spacingFactor: 1.5,
        fit: true,
        //circle: true,
        maximalAdjustments: 100,
        transform: (node,position) => { return {x: position.x, y: node.cy().height()-position.y} }
      },
      //layout: { name: 'cose' }

      layout: { name: 'dagre',
        spacingFactor: 1.5,
        padding: 60,
        //fit: false,
        transform: (node,position) => { return {x: position.x, y: node.cy().height()-position.y} }

      }
  });

cy_basis.collection('edge').on('mouseover', (evt) => {
  evt.target.addClass('hover');
});

cy_basis.collection('edge').on('mouseout', (evt) => {
  evt.target.removeClass('hover');
});


};

document.addEventListener('DOMContentLoaded', function() {


function step2(ts) {

  if (window.cy_graphs) {

    _.each(cy_graphs, (g,id) => {
      //let id = g.graph().id;
      let host_node = cy_basis.nodes('#'+id);
      if (host_node.length == 0) {
        return;
      }
      let pos = host_node.renderedPosition(),
      w = host_node.renderedWidth(),
      h = host_node.renderedHeight();

      //ccy.zoom({level:cy.zoom(),renderedPosition:{x:pos.x-w/2, y:pos.y-h/2}});
      g.container().style.left = pos.x - w/2;
      g.container().style.top = pos.y - h/2;
      g.container().style.width = w;
      g.container().style.height = h;

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

    });
  }

  window.requestAnimationFrame(step2);
}


window.requestAnimationFrame(step2);

});
