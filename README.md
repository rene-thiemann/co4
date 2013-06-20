# CO4 - complexity concerned constraint compiler

## Prerequisites

- [Haskell plattform] (http://www.haskell.org/platform/) with `ghc >= 7.6.1`
- [Minisat] (https://github.com/niklasso/minisat.git)
- [Minisat C bindings] (https://github.com/niklasso/minisat-c-bindings)
- [Minisat Haskell bindings] (https://github.com/niklasso/minisat-haskell-bindings)
- [Satchmo-core] (https://github.com/apunktbau/satchmo-core)

All other dependencies are available on Hackage and will be installed by 
cabal during the next step.

## Building

    cabal install

## Running

[CO4/Example/Binary.standalone.hs] (https://github.com/apunktbau/co4/tree/master/CO4/Example/Binary.standalone.hs)
implements addition and multiplication of binary values:

    fullAdder :: Bit -> Bit -> Bit -> (Bit,Bit)
    fullAdder a b carry =
      let xorAB = xor a b
      in
        ( xor xorAB carry
        , xor (a && b) (carry && xorAB)
        )

    halfAdder :: Bit -> Bit -> (Bit,Bit)
    halfAdder a b = (xor a b, a && b)

    mult :: Nat -> Nat -> (Nat,Bit)
    mult a b = case a of
      []     -> ([],False)
      (x:xs) -> 
        let multResult  = mult xs b
            shiftResult = withCarry shiftRight multResult
        in
          case x of
            False -> shiftResult
            True  -> withCarry (add b) shiftResult
    ...

The toplevel constraint `constraint r (a,b)` is satisfied if 

 - `a * b = r` (without an overflow) and
 - `a > 1` and
 - `b > 1`

So:

    constraint r (a,b) = case mult a b of
      (result,carry) -> and [ result == r
                            , not (trivial a)
                            , not (trivial b)
                            , not carry
                            ]

[CO4/Example/Binary.hs] (https://github.com/apunktbau/co4/tree/master/CO4/Example/Binary.hs)
loads and compiles 
[CO4/Example/Binary.standalone.hs] (https://github.com/apunktbau/co4/tree/master/CO4/Example/Binary.standalone.hs)
using Template-Haskell:

    $( runIO $ configurable [ImportPrelude] $ compileFile "CO4/Example/Binary.standalone.hs" )

Every definition `d` of the original program is compiled to an encoded
definition `encD`, i.e. the compiled constraint system `main` is `encMain`.

As we're using definitions of Haskell's prelude (`map`,`foldl`,etc.), 
we pass the compiler flag `ImportPrelude`.

Next, we need to setup an allocator for the unknown values.
Allocators for types of the prelude (`uList`,`uBool`) are provided by CO4.

    bitWidth  = 8
    uNat      = uList bitWidth uBool

As `main` is a constraint over a pair of naturals, the final allocator is

    allocator = uTuple2 uNat uNat

Finally, we want to solve the compiled constraint system `encMain`.
CO4 provides several solving functions, e.g.
`solveAndTestBooleanP :: [...] -> k -> Allocator -> ParamConstraintSystem m Boolean -> (k -> a -> b) -> IO (Maybe a)`
solves a parametrized constraint system with 

 - `k` being the parameter
 - `(k -> a -> b)` being the original constraint system. The found solution is
 checked against this function in order to verify the solution.

In the main `constraint` we seek a factorization for a given natural number `x` of
bit-width `bitWidth` using the previously defined allocators:

    solution <- solveAndTestBooleanP (toBinary (Just bitWidth) x) booleanCache allocator encMain main 

If there is a factorization, we want to decode the factors to decimal numbers:

    result :: Int -> IO (Maybe (Int,Int))
    result x = do
      solution <- solveAndTestBooleanP (toBinary (Just bitWidth) x) booleanCache allocator encMain main 
      case solution of
        Nothing    -> return Nothing
        Just (a,b) -> return $ Just (fromBinary a, fromBinary b)
  
We call `result` in a ghci session to find a factorization of 143:

    $ ghci CO4/Example/Binary.hs
    *CO4.Example.Binary> result 143
    Start producing CNF
    Cache call hits: 274 (9%), call misses: 2649 (90%)
    Cache case hits: 72 (2%), case misses: 2485 (97%)
    Assertion: 106176
    CNF finished (#variables: 53092, #clauses: 140028)
    Starting solver
    Solver finished in 0.499999 seconds (result: True)
    Starting decoder
    Decoder finished
    Solution: ([True,False,True,True,False,False,False],[True,True,False,True,False,False,False,False])
    Test: True
    Just (13,11)

For more examples see [CO4/Example] (https://github.com/apunktbau/co4/tree/master/CO4/Example).
