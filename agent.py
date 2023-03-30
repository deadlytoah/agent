import zmq

def error(socket, message):
    socket.send_multipart([b"ERROR", message])

def list_commands():
    return list(COMMAND_MAP.keys())

def command_map():
    return {
        "help": list_commands,
    }

def main():
    context = zmq.Context()

    # Create a socket for the server
    socket = context.socket(zmq.REP)
    socket.bind("tcp://*:0")

    # Print the port number to stdout
    port = socket.getsockopt(zmq.LAST_ENDPOINT).decode().rsplit(":", 1)[-1]
    print(port)

    while True:
        try:
            # Wait for a request from a client
            message = socket.recv_multipart()

            command = message[0].decode()
            arguments = [arg.decode() for arg in message[1:]]

            # Process the request
            if command in command_map():
                response = command_map()[command]()

                # Send the response back to the client
                socket.send_multipart([b"OK"] + response)
            else:
                error(socket, b"unknown command")
                response = nil

        except KeyboardInterrupt:
            break
        except Exception as e:
            # Handle any errors that occur during processing
            error_response = str(e).encode()
            error(socket, error_response)

if __name__ == '__main__':
    main()
