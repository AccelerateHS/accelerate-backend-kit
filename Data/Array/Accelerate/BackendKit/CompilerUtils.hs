

-- | This module defines some simple utilities for building compilers as chains of passes.
--
--   The reason for representing compilers this way is to enable
--   debugging printout and profiling.  That is, it's better for a
--   compiler to be a structured pipeline of passes, rather than an
--   opaque composition of functions.

module Data.Array.Accelerate.BackendKit.CompilerUtils
       (runPass, runOptPass, shapeName)
       where

import           Text.PrettyPrint.GenericPretty (Out(doc), Generic)
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S

----------------------------------------------------------------------------------------------------
-- Compiler Conventions and global constants:


-- | Given the name of an array variable, what is the name of the
-- variable which will contain its shape.
shapeName :: S.Var -> S.Var
shapeName avr = S.var (show avr ++ "_shape")

----------------------------------------------------------------------------------------------------

-- Pass composition:
runPass :: Out a => String -> (t -> a) -> t -> a
runPass msg pass input =
  S.maybtrace ("\n" ++ msg ++ ", output was:\n"++
                       "================================================================================\n"
                       ++ show (doc x)) 
  x
 where x = pass input              


-- An [optional] optimization pass:
runOptPass :: Out a => String -> (t -> a) -> (t -> a) -> t -> a
runOptPass str pass _otherwise = runPass str pass


-- TODO: Enable profiling support and a more sophisticated runtime representation of Compilers.



