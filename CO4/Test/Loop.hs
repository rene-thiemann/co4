{-# OPTIONS_CO4 SizedList Nat50 (SizedStep Nat15 Nat4 Nat4 Nat15) #-}

-- should find the looping derivation
-- abb -> bbaab -> bbabbaa

main d = looping_derivation g03 d

-- rewriting system  ab -> bbaa.

rs1 = RS (Cons (Rule (Cons A(Cons B (Cons B Nil)))
                    (Cons B(Cons B (Cons A (Cons A (Cons B Nil))))))
          Nil)


-- has loop of length 15, cf.
-- http://termcomp.uibk.ac.at/termcomp/competition/resultDetail.seam?resultId=288357&cid=3093
g03 = RS 
   (Cons (Rule (Cons A(Cons A(Cons A(Cons A Nil))))
               (Cons A(Cons A(Cons B(Cons B Nil)))))
   (Cons (Rule (Cons B(Cons A(Cons A(Cons B Nil))))
               (Cons A(Cons A(Cons B(Cons A Nil)))))
         Nil))

-- no known loop (?)
g06 = RS 
   (Cons (Rule (Cons A(Cons A(Cons A(Cons A Nil))))
               (Cons A(Cons B(Cons A(Cons B Nil)))))
   (Cons (Rule (Cons B(Cons A(Cons A(Cons B Nil))))
               (Cons A(Cons B(Cons A(Cons A Nil)))))
         Nil))

g10 = RS 
   (Cons (Rule (Cons A(Cons A(Cons A(Cons A Nil))))
               (Cons A(Cons B(Cons B(Cons B Nil)))))
   (Cons (Rule (Cons B(Cons A(Cons A(Cons B Nil))))
               (Cons A(Cons A(Cons B(Cons A Nil)))))
         Nil))

g13 = RS 
   (Cons (Rule (Cons A(Cons A(Cons A(Cons A Nil))))
               (Cons A(Cons B(Cons B(Cons B Nil)))))
   (Cons (Rule (Cons B(Cons A(Cons B(Cons B Nil))))
               (Cons A(Cons B(Cons B(Cons A Nil)))))
         Nil))

g19 = RS 
   (Cons (Rule (Cons A(Cons A(Cons A(Cons A Nil))))
               (Cons B(Cons A(Cons B(Cons B Nil)))))
   (Cons (Rule (Cons B(Cons A(Cons A(Cons B Nil))))
               (Cons A(Cons A(Cons B(Cons A Nil)))))
         Nil))

g20 = RS 
   (Cons (Rule (Cons A(Cons A(Cons A(Cons A Nil))))
               (Cons B(Cons A(Cons B(Cons B Nil)))))
   (Cons (Rule (Cons B(Cons A(Cons A(Cons B Nil))))
               (Cons A(Cons B(Cons A(Cons A Nil)))))
         Nil))


data Bool = False | True

or2 x y = case x of
    False -> y
    True  -> x

and2 x y = case x of
    False -> x
    True  -> y

not x  = case x of
    False -> True
    True -> False

data Sigma = A | B

eqSigma x y = case x of
    A -> case y of
        A -> True
        B -> False
    B -> case y of
        A -> False
        B -> True

data List a = Nil | Cons a (List a)

null xs = case xs of
    Nil -> True
    Cons x xs -> False

head xs = case xs of
    Nil -> undefined
    Cons x xs -> x

last xs = case xs of
    Nil -> undefined
    Cons x xs -> case xs of
        Nil -> x
        Cons x ys -> last xs

eqListSigma xs ys = case xs of
    Nil -> case ys of
        Nil -> True
        Cons y ys -> False
    Cons x xs -> case ys of
        Nil -> False
        Cons y ys -> 
            and2 (eqSigma x y) (eqListSigma xs ys)

append xs ys = case xs of
    Nil -> ys
    Cons x xs -> Cons x (append xs ys)

factor xs ys = or2 (prefix xs ys ) ( case ys of
    Nil -> False
    Cons y ys -> factor xs ys )

prefix xs ys = case xs of
    Nil -> True
    Cons x xs -> case ys of
        Nil -> False
        Cons y ys -> 
            and2 (eqSigma x y) (prefix xs ys)

foldr f z xs = case xs of
    Nil -> z
    Cons x xs -> f x (foldr f z xs)

map f xs = foldr ( \ x y -> Cons (f x) y ) Nil xs

or  xs = foldr or2 False xs
and xs = foldr and2 True xs

forall xs f = and ( map f xs )
exists xs f = or  ( map f xs )

data Rule = Rule (List Sigma) (List Sigma)

eqRule u1 u2 = case u1 of
        Rule l1 r1 -> case u2 of
            Rule l2 r2 -> 
                and2 (eqListSigma l1 l2)
                     (eqListSigma r1 r2)

data RS = RS (List Rule)

data Step = Step (List Sigma) -- prefix
                 Rule
                 (List Sigma) -- suffix

-- type Derivation = List Step

looping_derivation rs d =
   and2 (derivation_is_nonempty d)
    ( and2 (derivation_uses_rules rs d)
      (and2 (derivation_is_joinable d)
           (derivation_is_looping d)))

derivation_uses_rules rs d = case rs of
    RS rules -> forall d
        ( \ s -> step_uses_rules rules s )

derivation_is_nonempty d = not (null d)

derivation_is_looping d = 
      factor (left_semantics (head d))
           (right_semantics (last d))

derivation_is_joinable d = case d of
    Nil -> True
    Cons s1 later1 -> case later1 of
        Nil -> True
        Cons s2 later2 -> 
            and2 (joinable_steps s1 s2)
                 (derivation_is_joinable later1)

-- TODO: this is what I want to write:
-- right_semantics (Step p (Rule l r) s) = 
--    append p (append r s)

left_semantics step = case step of
    Step p u s -> case u of
        Rule l r -> append p (append l s)

right_semantics step = case step of
    Step p u s -> case u of
        Rule l r -> append p (append r s)

joinable_steps step1 step2 = 
    eqListSigma (right_semantics step1)
                (left_semantics  step2)

step_uses_rules rules step = case step of
   Step p u s -> 
       exists rules ( \ v -> eqRule u v )

