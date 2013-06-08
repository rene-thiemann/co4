{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
module CO4.EncodedAdt
  ( IntermediateAdt (..), EncodedAdt (..)
  , flags, isDefined, isUndefined, isConstantlyDefined, isConstantlyUndefined
  , caseOfBits)
where

import           Prelude hiding (and,undefined)
import           Control.Exception as Exception
import           Control.Monad (forM,zipWithM)
import           Data.List (transpose)
import           Data.Maybe (fromMaybe,catMaybes)
import           Satchmo.Core.Primitive (Primitive,constant,implies,and,select)
import qualified Satchmo.Core.Primitive as P
import           Satchmo.Core.Decode (Decode)
import           Satchmo.Core.MonadSAT (MonadSAT)
import           CO4.Util (bitWidth,binaries,for)

data IntermediateAdt p = IntermediateConstructorIndex Int [p]
                       | IntermediateUndefined

class Primitive p => EncodedAdt e p where

  -- |Builds an undefined encoded ADT
  undefined :: e p

  -- |Gets an ADT's flags. Is undefined if ADT is undefined.
  -- See `flags` for safe version.
  flags' :: e p -> [p]

  definedness :: e p -> p

  constantConstructorIndex :: e p -> Maybe Int

  caseOf :: MonadSAT m => e p -> [e p] -> m (e p)

  encodedConstructor :: Int -> Int -> [e p] -> e p

  constructorArgument :: Int -> Int -> e p -> e p

  toIntermediateAdt :: (MonadSAT m, Decode m p Bool) 
                    => e p -> Int -> m (IntermediateAdt (e p))

flags :: EncodedAdt e p => e p -> Maybe [p]
flags adt | not (isConstantlyUndefined adt) = Just $ flags' adt
flags _                                     = Nothing

isDefined,isUndefined :: EncodedAdt e p => e p -> Maybe Bool
isDefined   = P.evaluateConstant . definedness
isUndefined = fmap not . isDefined

isConstantlyDefined,isConstantlyUndefined :: EncodedAdt e p => e p -> Bool
isConstantlyDefined   = fromMaybe False . isDefined
isConstantlyUndefined = fromMaybe False . isUndefined

caseOfBits :: (MonadSAT m, Primitive p) => [p] -> [Maybe [p]] -> m [p]
caseOfBits flags branchBits = 
    Exception.assert (not $ null nonBottomBits) 
  $ Exception.assert (length flags == bitWidth (length branchBits)) 
  $ do
    premises <- mkPremises
    forM (transpose branchBits') $ mkBits premises
    where
      nonBottomBits  = catMaybes branchBits
      branchBitWidth = maximum $ map length nonBottomBits 
      branchBits'    = for branchBits $ \case
        Nothing -> replicate branchBitWidth $ constant False
        Just bs -> bs ++ replicate (branchBitWidth - (length bs)) (constant False)
      mkPremises     = mapM mkPremise patterns 
        where 
          patterns          = binaries $ length flags 
          mkPremise pattern = and $ zipWith select pattern flags

      mkBits premises bitsT = zipWithM implies premises bitsT >>= and

