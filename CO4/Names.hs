{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
-- |Namelike definitions
module CO4.Names 
  ( Namelike (..), convertName, funName, listName, consName, eqName, tupleName
  , nat8Name, nat8TypeName, intName, boolName, mainName, deprecatedMainName
  )
where

import           CO4.Language (Name(..),UntypedName(..))
import qualified Language.Haskell.TH as TH

class Namelike a where
  readName    :: String -> a
  fromName    :: a -> String

  mapName     :: (String -> String) -> a -> a
  mapName f   =  readName . f . fromName

  untypedName :: a -> UntypedName
  untypedName =  UntypedName . fromName

  name        :: a -> Name
  name        =  NUntyped . fromName

instance Namelike String where
  readName    = id
  fromName    = id

instance Namelike UntypedName where
  readName                    = UntypedName
  fromName  (UntypedName n)   = n

instance Namelike Name where
  readName                 = NUntyped
  fromName (NUntyped n)    = n
  fromName (NTyped n _)    = n
  mapName f (NUntyped n)   = NUntyped $ f n
  mapName f (NTyped n s)   = NTyped (f n) s
  name                     = id

instance Namelike TH.Name where
  readName = TH.mkName
  fromName = show

convertName :: (Namelike n,Namelike m) => n -> m
convertName = readName . fromName

funName :: Namelike n => n
funName = readName "->"

listName :: Namelike n => n
listName = readName "[]"

consName :: Namelike n => n
consName = readName ":"

eqName :: Namelike n => n
eqName = readName "=="

tupleName :: Namelike n => Int -> n
tupleName i = readName $ "(" ++ replicate (i-1) ',' ++ ")"

nat8TypeName :: Namelike n => n
nat8TypeName = readName "Nat8"

nat8Name :: Namelike n => n
nat8Name = readName "nat8"

intName :: Namelike n => n
intName = readName "Int"

boolName :: Namelike n => n
boolName = readName "Bool"

mainName :: Namelike n => n
mainName = readName "constraint"

deprecatedMainName :: Namelike n => n
deprecatedMainName = readName "main"
