const Ws = require('ws');
const Http = require('http');

let ws_server = function({port, on_connect}) {

  let is_init = false;

  let handle = null;

  let send = (_type,_data=null) => {
    try {
      let [type,data] = (_data===null) ? ['log',_type] : [_type,_data];
      let msg = JSON.stringify({type,data});
      handle && handle.send(msg);
      console.log('Sent: ['+type+'] '+ data.substring(0,40) + (data.length < 40 ? "" : "..."));
    } catch(e) {
      if (e.message == 'not opened') {} else { throw e; }
    }
  }

  const server = Http.createServer();

  const out = {send};

  const wss = new Ws.Server({ server });

  server.listen(port, () => {
    console.log('Websocket listening on %d.', server.address().port);
  });

  wss.on('connection', (ws, req) => {
    handle = ws;

    ws.on('message', (message) => {
      console.log('Received: %s', message);
    });

    send('log', 'Connection established');

    on_connect(out);


  });

  return out;
};

module.exports = ws_server;
