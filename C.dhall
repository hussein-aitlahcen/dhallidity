let mkContract = ./MkContract.dhall

let A = ./A.dhall

let B = ./B.dhall

let Message = < A : A.Message | B : B.Message >

let Store = { A : A.Store, B : B.Store }

let handler =
      \(store : Store) ->
      \(message : Message) ->
        merge
          { A =
              \(message : A.Message) ->
                { A = A.handler store.A message, B = store.B }
          , B =
              \(message : B.Message) ->
                { B = B.handler store.B message, A = store.A }
          }
          message

in  mkContract
      Store
      Message
      { A.counter = 0xCAFEBABE, B = { a = 0xDEADC0DE, b = 0xBEEFBEEF } }
      handler
