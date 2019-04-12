module Error where

import Control.Monad.Except
import Data.Functor.Identity

type ErrInfo = String
type ErrT = ExceptT ErrInfo
type ErrM = ErrT Identity
