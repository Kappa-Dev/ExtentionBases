let ws_client = ({url,cb}) => {
  let ready = false;
  let connection = null;
  let interval = null;

  let retry = () => {
    ready = false;
    if(!interval) {
      interval = setInterval(connect,500);
    }
  }

  let connect = () => {
    if (connection) {
      connection.obsolete = true;
    }

    connection = new WebSocket(url);

    let that = connection;

    connection.onopen = () => {
      console.log("Connection opened");
      if (that.obsolete) { console.log("open: obsolete"); return; }
      ready = true;
      if (interval) {
        clearInterval(interval);
        interval = null;
      }
      console.log("New connection confirmed");
      connection.send('Connected');
    }

    connection.onmessage = (e) => {
      if (that.obsolete) { console.log("message: obsolete"); return; }


      let m = null;

      try {
        m = JSON.parse(e.data);
      } catch(err) {
        console.error("Cannot parse message: "+e.data);
        return;
      }

      if (!m.type) {
        console.error("No message type specified: "+e.data);
      } else {
        cb(m.type,m.data);
      }
    }

    connection.onclose = (e) => {
      if (that.obsolete) { console.log("close: obsolete"); return; }
      console.log("close");
      that.obsolete = true;
      retry();
    }

    connection.onerror = (e) => {
      if (that.obsolete) { console.log("error: obsolete"); return; }
      console.log("error");
      that.obsolete = true;
      retry();
    }
  }

  let send = (msg) => {
    if (ready) {
      connection.send(msg);
    }
  }

  return {connect,send};
};

module.exports = ws_client;

