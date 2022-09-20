let Env =
      \(Effect : Type) ->
      \(Address : Type) ->
        { callValue : Natural
        , callDataSize : Natural
        , codeSize : Natural
        , gasPrice : Natural
        , returnDataSize : Natural
        , coinbase : Address
        , timestamp : Natural
        , number : Natural
        , difficulty : Natural
        , gasLimit : Natural
        , chainId : Natural
        , selfBalance : Natural
        , baseFee : Natural
        , programCounter : Natural
        , mSize : Natural
        , gas : Natural
        , address : Address
        , origin : Address
        , caller : Address
        , balanceOf : Address -> Natural
        , mload : forall (T : Type) -> Natural -> T
        , mstore : forall (T : Type) -> T -> Natural -> Effect
        , callDataLoad : forall (T : Type) -> T
        , sload : forall (T : Type) -> Natural -> T
        , sstore : forall (T : Type) -> forall (x : T) -> Natural -> Effect
        , return : forall (T : Type) -> forall (x : T) -> Effect
        , sequence : List Effect -> Effect
        }

in  \(Store : Type) ->
    \(Message : Type) ->
    \(initial : Store) ->
    \(handler : Store -> Message -> Store) ->
    \(Effect : Type) ->
    \(Address : Type) ->
    \(env : Env Effect Address) ->
      env.sequence
        [ env.sstore Store initial 0
        , env.sstore
            Store
            (handler (env.sload Store 0) (env.callDataLoad Message))
            0
        ]
