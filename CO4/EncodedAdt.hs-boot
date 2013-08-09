module CO4.EncodedAdt
  (EncodedAdt,Primitive,makeWithStackTrace,encEmpty,flags)
where

import Satchmo.Core.Boolean (Boolean)
import CO4.Stack (CallStackTrace)

type Primitive = Boolean
data EncodedAdt

instance Eq  EncodedAdt
instance Ord EncodedAdt

makeWithStackTrace :: Int -> Primitive -> [Primitive] -> [EncodedAdt] -> CallStackTrace
                   -> EncodedAdt

encEmpty :: EncodedAdt

flags :: EncodedAdt -> Maybe [Primitive]
