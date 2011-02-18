module Parsable where

import Control.Applicative
import Text.Parsec hiding (many, (<|>))

type P a = Parsec String [String] a

-- | A type class for generic parsing. It's especially useful for
--   building Read instances from Parsec parsers.
class Parsable a where
  genParser :: P a
  readsPrecFromParser :: ReadS a
  readsPrecFromParser =
    either (fail . show) return .
      runParser ((,) <$> genParser <*> getInput) [] ""

