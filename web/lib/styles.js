module.exports = [ // the stylesheet for the graph
  {
    selector: 'node[inner]',
    style: {
      'label': 'data(label)',
      'text-halign': 'center',
      'text-valign': 'center',
      'events': 'no'
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
      //'opacity': 0.6,
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
      'background-color': '#666',
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
    selector: 'node[outer].activeCC, node[outer].activeCCLong',
    style: {
      'background-color': '#2ba7ef',
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
      'background-color': '#0654d3',
      'background-opacity': 0.2,
    }
  },
  {
    selector: 'node[outer].hover',
    style: {
      //'border-color': '#0654d3',
      'background-color': '#0654d3',
      //'border-width': '10px',
      'background-opacity': 0.3,
      'border-opacity': 1
    }
  },
  {
    selector: 'edge[outer]',
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
    selector: "edge[outer][conflict]",
    style: {
      'line-style': 'dashed',
      'width': 1,
      'line-color': '#A0A0A0',
      'visibility': 'hidden'
      //'curve-style': 'unbundled-bezier'
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
      color: '#27db20'
    }
  },
  {
    selector: 'edge[outer][conflict].hover',
    style: {
      opacity: 0.9,
      width: 7,
      color: '#505050'
    }
  },
  {
    selector: 'edge[outer].activeCC, edge[outer].activeCCLong',
    style: {
      opacity: 0.8,
      width: 7,
    }
  },
  {
    selector: 'edge[outer].activeCC',
    style: {
      opacity: 1,
      color: '#0e540b',
      width: 7,
    }
  },
  {
    selector: 'edge[outer][conflict].activeCC, edge[outer][conflict].activeCCLong',
    style: {
      'line-color': '#808080',
      width: 7,
    }
  },
  {
    selector: 'edge[outer][conflict].activeCC',
    style: {
      'line-color': '#404040',
      width: 7,
    }
  },

];
