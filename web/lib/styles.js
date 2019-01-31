const outer = {
  background: {
    idle: '#666',
    active: '#2ba7ef',
    hover: '#0654d3',
  },
  edge: {
    conflict: {
      line: {
        //idle: '#A0A0A0',
        //hover: '#505050',
        //active: '#808080',
        //activeLong: '#404040',
        idle: '#b5342d',
        hover: '#b5342d',
        active: '#b5342d',
        activeLong: '#b5342d'
      }
    },
    line: {
      idle: '#1a8416',
      active: '#0a3007',
      hover: '#27db20'
    },
    arrow: {
      idle: '#ccc',
    }
  }
};

module.exports = [ // the stylesheet for the graph
  {
    selector: 'node:active',
    style: {
      //'overlay-padding': 0
      //'overlay-opacity': 0
    }
  },
  {
    selector: 'node[inner]',
    style: {
      'label': 'data(label)',
      'text-halign': 'center',
      'text-valign': 'center',
      'events': 'no',
      'font-size': '10px'
    }
  },
  {
    selector: 'node[inner][highlight]',
    style: {
      'background-color': e => colors.get(e.data("highlight")),
    }
  },
  {
    selector: 'edge[inner]',
    style: {
      'source-label': 'data(taillabel)',
      'target-label': 'data(headlabel)',
      'curve-style': 'bezier',
      'source-text-offset': '0.5em',
      'target-text-offset': '0.5em'
    }
  },
  {
    selector: 'node[outer]',
    style: {
      'background-color': outer.background.idle,
      'background-opacity': 0,
      'border-width': '2px',
      'border-style': 'solid',
      'border-color': 'black',
      'border-opacity': 0.05,
      'label': 'data(id)',
      'width': '200px',
      'height': '200px',
      'font-size': '28px',
      'label': 'data(label)',
      'shape': 'square'
    }
  },

  {
    selector: 'node.localnode',
    style: {
      'font-size': 'data(fontSize)'
    }
  },
  {
    selector: 'edge.localedge',
    style: {
      'font-size': 'data(fontSize)',
      'source-text-offset': 'data(sourceTextOffset)',
      'target-text-offset': 'data(targetTextOffset)',
    }
  },
  {
    selector: 'node[outer].activeCC, node[outer].activeCCLong',
    style: {
      'background-color': outer.background.active,
      'background-opacity': 0.1,
      'border-opacity': 0.1,
    }
  },
  {
    selector: 'node[outer].activeCC',
    style: {
      'border-opacity': 1
    }
  },
  {
    selector: 'node[outer].hoverLong',
    style: {
      'background-color': outer.background.hover,
      'background-opacity': 0.4,
    }
  },
  {
    selector: 'node[outer].hover',
    style: {
      'background-color': outer.background.hover,
      'background-opacity': 0.3,
      'border-opacity': 1
    }
  },
  {
    selector: 'edge[outer]',
    style: {
      'width': 2,
      'line-color': outer.edge.line.idle,
      'line-style': 'solid',
      'opacity': '0.7',
      'target-arrow-color': outer.edge.arrow.idle,
      'target-arrow-shape': 'triangle',
      'curve-style': 'unbundled-bezier'
    },
  },
  {
    selector: 'edge[outer][conflict]',
    style: {
      'target-arrow-shape': 'none'
    },
  },
  {
    selector: "edge[outer][conflict]",
    style: {
      'line-style': 'dashed',
      'width': 1,
      'line-color': outer.edge.conflict.line.idle,
      'visibility': 'hidden'
      //'curve-style': 'unbundled-bezier'
    }

  },
  {
    selector: "edge[outer].defaultHide",
    style: {
      'visibility': 'hidden'
    }
  },
  {
    selector: "edge[outer][conflict].activeCC.visible, edge[outer][conflict].activeCCLong.visible",
    style: {
      'visibility': 'visible'
    }
  },
  {
    selector: 'edge[outer][^conflict].hover',
    style: {
      opacity: 0.9,
      width: 7,
      'line-color': outer.edge.line.hover,
    }
  },
  {
    selector: 'edge[outer][conflict].hover',
    style: {
      opacity: 0.9,
      width: 7,
      'line-color': outer.edge.conflict.line.hover,
    }
  },
  {
    selector: 'edge[outer][^conflict].activeCC, edge[outer][^conflict].activeCCLong',
    style: {
      'visibility': 'visible',
      opacity: 0.8,
      width: 7,
    }
  },
  {
    selector: 'edge[outer][^conflict].activeCC',
    style: {
      'visibility': 'visible',
      opacity: 1,
      'line-color': outer.edge.line.active,
      width: 7,
    }
  },
  {
    selector: 'edge[outer][conflict].activeCCLong',
    style: {
      'line-color': outer.edge.conflict.line.active,
      width: 7,
    }
  },
  {
    selector: 'edge[outer][conflict].activeCC',
    style: {
      'line-color': outer.edge.conflict.line.activeLong,
      width: 7,
    }
  },

];
