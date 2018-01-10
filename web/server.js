const Http = require('http');
const Express = require('express');
const Ws = require('ws');
const Chokidar = require('chokidar');
const Fs = require('fs');
const config = {
  ports: { http: 3000, ws: 3001 }
};

const path = require('path');

const app = Express();
let basis_file = path.join(path.dirname(__dirname),'web_eb.dot');
console.log(basis_file);
let watch = Chokidar.watch(basis_file);

app.use('/',Express.static(__dirname));

let sendBasis = websocket => () => {
  Fs.readFile(basis_file,'utf8', (err,data) => {
    websocket.send('graph',data);
  });
}



let ws_server = function({on_connect}) {

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

  server.listen(config.ports.ws, () => {
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
}({on_connect: ws => sendBasis(ws)()});


watch.on('change',sendBasis(ws_server)).on('add',sendBasis(ws_server));

app.listen(config.ports.http, () => {
  console.log('Web server listening on port %d.',config.ports.http)
});
