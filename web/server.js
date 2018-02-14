const Express = require('express');
const Chokidar = require('chokidar');
const Fs = require('fs');
const Path = require('path');
const WSServer = require('./lib/ws-server');
const config = {
  ports: { http: 3000, ws: 3001 }
};

const app = Express();

const basis_file = Path.join(Path.dirname(__dirname),'web_eb.dot');

const watch = Chokidar.watch(basis_file);

let sendBasis = websocket => {
  Fs.readFile(basis_file,'utf8', (err,data) => {
    websocket.send('graph',data);
  });
}

let ws_server = WSServer({
  port: config.ports.ws,
  on_connect: sendBasis
});

watch.on('change',() => sendBasis(ws_server))
watch.on('add', () => sendBasis(ws_server));

app.use('/',Express.static(__dirname));
app.listen(config.ports.http, () => {
  console.log('Web server listening on port %d.',config.ports.http)
});

process.on('uncaughtException', function(err) {
  console.log("UNCAUGHT EXCEPTION");
  console.log(err.stack)
  console.log("_______________________");
});
