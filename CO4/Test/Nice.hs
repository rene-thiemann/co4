{-# language TemplateHaskell #-}
{-# language FlexibleInstances #-}

import Prelude hiding (Left, Right)
import Autolib.ToDoc

data List a = Nil | Cons a (List a)

toList l = case l of
    Nil -> [] ; Cons x xs -> x : toList xs

instance ToDoc a => ToDoc (List a) where
    toDoc = toDoc . toList

data Sigma = A | B 

type Word = List Sigma

data Rule = Rule { lhs :: Word, rhs :: Word }

data Step = Step { prefix :: List Sigma
                 , rule :: Rule
                 , suffix :: List Sigma
                 }

data Side = Left | Right

data Overlap = Overlap { side :: Side, pre :: Word, suf :: Word, c1 :: Rule, c2 :: Rule }

data Move = Move { origin :: List Sigma
                 , image :: List (List Sigma)
                 , derivation :: List Step
                 }

-- type Morphism = (List Move)

data Transport = Transport { pivot :: List Sigma
                           , morphism :: List Move
                           , start :: List Sigma
                           , iterated :: List (List Sigma)
                           }

derives [makeToDoc] [''Sigma, ''Rule, ''Step, ''Side, ''Overlap, ''Move, ''Transport]

instance Show (List Step) where show = render . toDoc
instance Show Transport where show = render . toDoc