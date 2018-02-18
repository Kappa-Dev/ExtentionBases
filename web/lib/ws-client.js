let ws_client = ({url,cb}) => {
  let connection = null;
  let timeout = null;
  let connection_counter = 0;
  let debug = false;

  let _log = (str) => { if (debug) { console.log(str); } }


  let retry = () => {
    if (!connection || connection.obsolete || connection.readyState !== WebSocket.OPEN) {
      if (!timeout) {
        _log("[retry: closed, no timeout]");
        connect();
        timeout = setTimeout(() => { timeout = null; retry(); },2000);
      } else {
        _log("[retry: closed, has timeout]");
      }
    } else {
      _log("[retry: open]");
    }
  }

  let connect = () => {

    if (connection) {
      connection.close();
    }

    that = new WebSocket(url);
    connection = that;
    let current_counter = connection_counter++;
    let log = str => _log(`[${current_counter}${that.obsolete ? ' obsolete' : ''}]: ${str}`)

    that.onopen = () => {
      log("open start");
      if (that.obsolete) return;
      log("open: confirmed");
      that.send('Connected');
    }

    that.onmessage = (e) => {
      log("message received");
      if (that.obsolete) return;

      let m = null;

      try {
        m = JSON.parse(e.data);
      } catch(err) {
        log("Cannot parse message: "+e.data);
        return;
      }

      if (!m.type) {
        log("No message type specified: "+e.data);
      } else {
        cb(m.type,m.data);
      }
    }

    that.onclose = (e) => {
      log("close");
      that.obsolete = true;
      retry();
    }

    that.onerror = (e) => {
      log("error");
      if (that.obsolete) return;
      that.obsolete = true;
      retry();
    }
  }

  let send = (msg) => {
    if (connection && !connection.obsolete) {
      connection.send(msg);
    }
  }

  return {connect,send};
};

module.exports = ws_client;

