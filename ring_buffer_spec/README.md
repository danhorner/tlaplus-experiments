### `reader_writer.tla`: The abstract specification

reader_writer defines a world where messages from an alphabet are sent and received on
a channel. It defines transitions to send messages, appending them to `messages_sent` and 
then also to read messages, which increases the count.


### `ring_buffer.tla`: The implementation

Ring buffer defines reader and writer processes that pass messages through a circular buffer. We instatiate `reader_writer` 
and ask the model checker to verify that `ring_buffer` is a a faithful implementation of the reader-writer spec.
