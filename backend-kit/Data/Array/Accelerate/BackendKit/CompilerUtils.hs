

-- | This module defines some simple utilities for building compilers as chains of passes.
--
--   The reason for representing compilers this way is to enable
--   debugging printout and profiling.  That is, it's better for a
--   compiler to be a structured pipeline of passes, rather than an
--   opaque composition of functions.

module Data.Array.Accelerate.BackendKit.CompilerUtils
       (
         -- * Compiler construction, compiler conventions, and global constants:
         runPass, runOptPass,
         shapeName, sizeName, isShapeName, isSizeName,

        -- * Debugging     
        maybtrace, tracePrint, dbg -- Flag for debugging output.
       )
       where

import           Text.PrettyPrint.GenericPretty (Out(doc))
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Debug.Trace        (trace)
import           System.IO.Unsafe   (unsafePerformIO)
import           System.Environment (getEnvironment)

----------------------------------------------------------------------------------------------------
-- Compiler Conventions and global constants:
----------------------------------------------------------------------------------------------------

-- TODO: Move this to Helpers.hs

-- | Given the name of an array variable, what is the name of the variable which will
-- contain its shape.  This variable will refer to a tuple for rank>1 arrays.
shapeName :: S.Var -> S.Var
shapeName avr = S.var (show avr ++ "_shape")

isShapeName :: S.Var -> Bool
isShapeName v = reverse "_shape" == take 6 (reverse$ show v)

-- | Given the name of an array variable, what is the name of the variable which will
-- contain its SIZE.  This variable will always be of type TInt.
sizeName :: S.Var -> S.Var
sizeName avr = S.var (show avr ++ "_size")

isSizeName :: S.Var -> Bool
isSizeName v = reverse "_size" == take 5 (reverse$ show v)

------------------------------------------------------------
-- Compiler Construction:
------------------------------------------------------------

-- Pass composition:
runPass :: Out a => String -> (t -> a) -> t -> a
runPass msg pass input =
  maybtrace ("\n" ++ msg ++ ", output was:\n"++
                       "================================================================================\n"
                       ++ show (doc x)) 
  x
 where x = pass input              


-- An [optional] optimization pass:
runOptPass :: Out a => String -> (t -> a) -> (t -> a) -> t -> a
runOptPass str pass _otherwise = runPass str pass


-- TODO: Enable profiling support and a more sophisticated runtime representation of Compilers.


----------------------------------------------------------------------------------------------------
-- DEBUGGING
----------------------------------------------------------------------------------------------------

-- | Debugging flag shared by all accelerate-backend-kit modules.
--   This is activated by setting the environment variable DEBUG=1
dbg :: Bool
dbg = case lookup "DEBUG" unsafeEnv of
       Nothing  -> False
       Just ""  -> False
       Just "0" -> False
       Just _   -> True

unsafeEnv :: [(String,String)]
unsafeEnv = unsafePerformIO getEnvironment

-- | Print the value returned prefixed by a message.
tracePrint :: Show a => String -> a -> a
tracePrint s x = 
  if dbg then (trace (s ++ show x) x)
         else x

-- | Trace, but only if debugging is enabled.
maybtrace :: String -> a -> a
maybtrace = if dbg then trace else \_ -> id 
