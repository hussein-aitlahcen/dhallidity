let Message = < Rotate >

let Store = { a : Natural, b : Natural }

let handler =
      \(store : Store) ->
      \(message : Message) ->
        merge { Rotate = { a = store.b, b = store.a } } message

in  { Message, Store, handler }
