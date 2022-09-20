let Message = < Increment | Reset >

let Store = { counter : Natural }

let handler =
      \(store : Store) ->
      \(message : Message) ->
        { counter = merge { Increment = store.counter + 1, Reset = 0 } message }

in  { Message, Store, handler }
