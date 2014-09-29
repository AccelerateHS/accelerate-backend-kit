{-# LANGUAGE DeriveDataTypeable, OverloadedStrings, FlexibleInstances, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE CPP #-}

{-|
   This module provides a simple way to use HOAS (higher order abstract syntax) to emit C/C++ code.

   This approach adoesn't define a complete model for C++ code, just
   an easier way of emitting concretes syntax than using strings.

-}

module Data.Array.Accelerate.Shared.EasyEmit
  (
    -- * Types and entrypoints for Running EasyEmit computations
    EasyEmit, runEasyEmit, execEasyEmit, evalEasyEmit,

    -- * The syntax type.  The core type used to construct expressions via EasyEmit.
    Syntax(), fromSyntax, toSyntax, (+++), CType,
    
    -- * Functions for generating C/C++ Expressions:
    constant, stringconst, dot, arrow,
    (?), (.:), (>>), (<<), (&), (.|),
    dereference, addressOf, arrsub, arrset, (!), 
    Data.Array.Accelerate.Shared.EasyEmit.parens,
    
    -- * Functions for generating C/C++ Statements:
    emitStmt, block, set, (+=), (-=), if_, return_, sizeof, assert,
    for, forRange, forStridedRange, cilkForRange, cilkForStridedRange, 
    var, varinit, tmpvar, tmpvarinit, 
    
    -- * Defining functions in C/C++ code using HOAS.
    funDef, rawFunDef, rawFunDefProto, function, ObjFun, 

    -- * Defining types in C/C++
    cppStruct, 
    
    -- * Comments in generated code.
    comm,

    -- * Raw, unformatted output of lines.
    emitLine, 
    
    -- * Reexported standard Haskell functions.
    Num(..), Fractional(..), P.Eq(..), 
    
    -- * Overloaded Booleans operations
    -- (because native Haskell booleans aren't overloaded in the style of `Num`)
    Boolean(..),
    
    -- * Redefined `Ord` and `Eq` classes that uses the `Boolean` class.
    Ord(..)
    
  )
  where

import qualified  Control.Monad.State.Strict as S
import  Data.List       (intersperse)
import Data.Char        (showLitChar)
import GHC.Exts         (IsString(fromString))
import System.IO        (hPutStr, Handle)
import Text.PrettyPrint.HughesPJ as PP (Doc, text, (<>), (<+>), ($+$), int, lbrace, rbrace, colon, nest,
                                  empty, parens, semi, hcat, fcat, vcat, hsep, sep) 
import Text.PrettyPrint.HughesPJClass (Pretty, pPrint, render)
import qualified Prelude as P
import Prelude hiding ((&&), (||), (==), (/=), not, Eq
		       , Ord, (<), (<=), (>), (>=), (>>), max, min
		      )

#ifdef USE_STRINGTABLE
import StringTable.Atom (Atom, ToAtom(toAtom), fromAtom)
#endif
  
-- | C/C++ Types are just arbitrary text.
-- newtype CType = CType String
-- instance Pretty CType where  
--   pPrint (CType s) = text s
type CType = Syntax
instance Pretty CType where  
 pPrint (Syn s) = s
  
----------------------------------------------------------------------------------------------------
-- Monad plus HOAS (Higher-order-abstract-syntax) for C++
----------------------------------------------------------------------------------------------------

-- | A monad for generating syntax:
--   The state consists of an accumulator for lines of syntax, plus a counter for temporary variables.
newtype EasyEmit a = EE (S.State EEState a)
type EEState = ([Doc],Int)

-- | Run a syntax-emitting computation and render it to a document.
runEasyEmit :: EasyEmit a -> (a,Doc)
runEasyEmit m = (a,b)
 where (a,_,b) = rawRunEasyEmit 0 m

-- | This full version returns the unique-variable-counter as well.
rawRunEasyEmit :: Int -> EasyEmit a -> (a, Int, Doc)
rawRunEasyEmit start (EE m) = (a, cnt, vcat (reverse ls))
 where 
  (a,(ls,cnt)) = S.runState m ([], start)

-- | Following the conventions of `State` monads, this executes just for the document.
execEasyEmit :: EasyEmit a -> Doc
execEasyEmit = snd . runEasyEmit

-- | Following the conventions of `State` monads, this evaluates just for the result value.
evalEasyEmit :: EasyEmit a -> a
evalEasyEmit = fst . runEasyEmit 


-- This runs a subcomputation only for value -- discards its emission side effects.
_forValueOnly :: EasyEmit a -> EasyEmit a
_forValueOnly (EE m) =
 do (ls,c) <- S.get 
    let (val,(_,c2)) = S.runState m ([], c)
    S.put (ls,c2)
    return val

-- BOILERPLATE, because of newtype rather than type synonym for EasyEmit:
instance Monad EasyEmit where
  -- Whew, need to verify that this has no perfermance overhead:
  (EE ma) >>= fn = EE (ma >>= (\x -> case fn x of EE m -> m))
  return x       = EE (return x)
instance S.MonadState EEState EasyEmit where
  get   = EE S.get
  put x = EE (S.put x)

instance StringBuilder EasyEmit where 
--instance StringBuilder (S.State ([Doc], Int)) where 
  putS s = S.modify (\ (ls,cnt) -> (text s:ls, cnt) )
  runSB (EE m) = 
      let (res, (ls,_cnt)) = S.runState m ([],0) 
      in (render$ vcat$ reverse ls, res)


--------------------------------------------------------------------------------
-- First, simple helpers / utilities:
--------------------------------------------------------------------------------

instance P.Eq Doc where
  -- Would be nice to memoize this!
  a == b  =  render a P.== render b

-- | The abstract type of syntax objects.  (The EasyEmit monad uses
--   this internally.)  If you wish to construct a `Syntax`, use
--   `constant` to convert a `String`.
data Syntax = Syn Doc
  deriving (Show, P.Eq)

#ifdef USE_STRINGTABLE
instance ToAtom Syntax where
   toAtom d = toAtom$ fromSyntax d
atomToSyn = Syn . text . fromAtom
-- Also, overloading the string constants themselves is nice:
-- instance IsString Doc where -- Now this is in 'pretty' itself
--     fromString s = text s
instance IsString Atom where
    fromString s = toAtom s
instance ToAtom Doc where
   toAtom d = toAtom$ render d
instance SynChunk Atom where 
  toDoc = text . fromAtom
#endif

-- | Retrieve a formatted (pretty-printed) document from a piece of Syntax.
fromSyntax :: Syntax -> Doc
fromSyntax (Syn s) = s

-- | The inverse of fromSyntax.
toSyntax :: Doc -> Syntax 
toSyntax = Syn 


fromInt :: Int -> Syntax
fromInt  = Syn . int 

strToSyn :: String -> Syntax
strToSyn = Syn . text 

-- | Append two pieces of syntax.  This is effectively a string append; no spacing is added.
(+++) :: Syntax -> Syntax -> Syntax
(Syn a) +++ (Syn b) = Syn (a <> b)

-- | The dot-operator for struct/member/method dereference in C/C++.
--   @dot (constant "x") (constant "y")@ emits @x.y@
dot :: Syntax -> Syntax -> Syntax
(Syn a) `dot`   (Syn b) = Syn (a <> text "." <> b)

-- | Like the dot operator but use the @->@ for pointer dereference.
arrow :: Syntax -> Syntax -> Syntax
(Syn a) `arrow` (Syn b) = Syn (a <> text "->" <> b)

-- | Dereference a pointer, i.e. @dereference (constant "x")@ produces @(*x)@
dereference :: Syntax -> Syntax
dereference (Syn a) = Syn$ PP.parens (text "*" <> a)

-- | What is the address of a variable (l-value)? @addressOf (constant "x")@ produces @(&x)@.
addressOf :: Syntax -> Syntax
addressOf  (Syn a) = Syn$ PP.parens (text "&" <> a)

-- | Array subscript operator.  @arrsub a i@ returns the @i@-th element of array @a@.
arrsub :: Syntax -> Syntax -> Syntax
arrsub (Syn a) (Syn b) = Syn$ (a <> text "[" <> b <> text "]")

-- | An alias for the array subscript operator.  This enables
-- "arr ! i" expressions in the Haskell convention.
(!) :: Syntax -> Syntax -> Syntax
(!) = arrsub

-- | Emit a line of output. This implicitly appends a newline (but not a semi-colon).
emitLine :: Syntax -> EasyEmit ()
emitLine (Syn doc) = 
  do (ls,c) <- S.get
     S.put (doc : ls, c)

-- A bit ugly, this adds the chunk to the end of the previous line.
-- emitToPrevLine :: S.MonadState ([Doc], t) m => Syntax -> m ()
emitToPrevLine (Syn doc) = 
  do (ls,c) <- S.get
     S.put $ case ls of 
              []      -> (doc : ls, c)
	      (hd:tl) -> (hd <> doc : tl, c)

-- | Emit a piece of syntax as a statement, i.e. this Adds the semi-colon (and newline) at the end.
emitStmt :: Syntax -> EasyEmit ()
emitStmt (Syn doc) = emitLine (Syn$ doc <> semi)

-- Also, overloading the string constants themselves is nice:
instance IsString Syntax where
    fromString s = Syn (text s)


-- Comma separate Docs either horizontally or vertically:
-- TEMP: MAKING THIS HCAT FOR NOW UNTIL I CAN FIGURE OUT SOME OF THE INDENTATION PROBELMS:
commasep :: [Doc] -> Doc
commasep ls = hcat$ intersperse (text", ") ls

-- (This version includes PP.parens)
--pcommasep = PP.parens . commasep
pcommasep :: [Doc] -> Doc
pcommasep ls = PP.parens$ fcat$ intersperse (text", ") ls 

parens :: Syntax -> Syntax
parens (Syn d) = Syn $ PP.parens d


--------------------------------------------------------------------------------
-- C++ Expressions
--------------------------------------------------------------------------------

-- | C++ Conditional expressions, i.e. the @a ? b : c@ syntax.  This
--  should only be used WITH the @.:@ operator, which is a bastardization of @:@.
(?) :: Syntax -> Syntax -> Syntax
(Syn a) ?  (Syn b) = Syn ("(" <> a <> " ? " <> b )

-- | The second part of of a @a ? b .: c@ expression.
(.:) :: Syntax -> Syntax -> Syntax
-- Hack, these must always be used together to get balanced parens:
(Syn a) .: (Syn b) = Syn ( a <> " : " <> b  <> ")")

-- | Bitwise OR
(.|) :: Syntax -> Syntax -> Syntax
(Syn a) .| (Syn b) = Syn (PP.parens$ a <+> "|" <+> b)

-- | Bitwise AND
(&) :: Syntax -> Syntax -> Syntax
(Syn a) & (Syn b) = Syn (PP.parens$ a <+> "&" <+> b)

-- | Right shift.
(>>) :: Syntax -> Syntax -> Syntax
(Syn a) >> (Syn b) = Syn (PP.parens$ a <+> ">>" <+> b)

-- | Left shift
(<<) :: Syntax -> Syntax -> Syntax
(Syn a) << (Syn b) = Syn (PP.parens$ a <+> "<<" <+> b)


-- The most important class of expressions are generated by overloaded
-- standard operators, as follows:
instance Num Syntax where 
  (Syn a) + (Syn b) = Syn (PP.parens $ a <> " + " <> b )
  (Syn a) * (Syn b) = Syn (PP.parens $ a <> " * " <> b )
  (Syn a) - (Syn b) = Syn (PP.parens $ a <> " - " <> b )
  abs    (Syn a) = Syn ("abs" <> PP.parens a )
  negate (Syn a) = Syn (PP.parens ("-" <> PP.parens a))
  fromInteger n = Syn (text $ show n)
  -- Could implement this I suppose...
  signum _ = "__ERROR__"

instance Fractional Syntax where 
  (Syn a) / (Syn b) = Syn (PP.parens $ a <> " / " <> b )
  recip (Syn a) = Syn (PP.parens $ "1 / " <> a )
  fromRational rat = Syn ( text$ show rat )

instance Boolean Syntax where
    (Syn a) && (Syn b) = Syn (PP.parens $ a <> " && " <> b )
    (Syn a) || (Syn b) = Syn (PP.parens $ a <> " || " <> b )
    not (Syn a) = Syn ("!" <> PP.parens a )
    false = Syn "false"
    true  = Syn "true"

instance Ord Syntax Syntax where
    (Syn a) < (Syn b) = Syn (PP.parens $ a <> " < " <> b )
    (Syn a) > (Syn b) = Syn (PP.parens $ a <> " > " <> b )
    (Syn a) <= (Syn b) = Syn (PP.parens $ a <> " <= " <> b )
    (Syn a) >= (Syn b) = Syn (PP.parens $ a <> " >= " <> b )
    max (Syn a) (Syn b) = Syn ("max" <> pcommasep [a,b] )
    min (Syn a) (Syn b) = Syn ("min" <> pcommasep [a,b] )

--   conditional (Syn a) b c = Syn (PP.parens $ a <> " ? " <> b <> ":" <> c )

-- | Generalized Eq typeclass that is also parameterized over the
--   representation of booleans.
instance Eq Syntax Syntax where
    (Syn a) == (Syn b) = Syn (PP.parens $ a <> " == " <> b )   

-- | Use a string directly as C++ syntax.  This can be used for
-- literals or for any syntactic forms that are not supported directly
-- by this module.
constant :: String -> Syntax
constant = fromString

-- | Emit a C++ string expression, i.e. including double quotes.  The
--   argument to this function need NOT include double quotes.
stringconst :: String -> Syntax
stringconst str = Syn$ dubquotes$ escapeString str

-- new :: Syntax -> [Syntax] -> Syntax
-- new :: Type -> [Syntax] -> Syntax
-- new ty args = Syn$ "new" <+> (fromSyntax$ function (Syn$ pPrint ty) args)

-- | Sizeof function
sizeof :: Syntax -> Syntax
sizeof (Syn x) = Syn$ PP.parens$ "sizeof" <> PP.parens x

--------------------------------------------------------------------------------
-- Declaring variables
--------------------------------------------------------------------------------

-- | Create a variable binding using a particular name provided.
var :: CType -> Syntax -> EasyEmit Syntax
var ty (Syn name) = do emitStmt (Syn (pPrint ty <+> name ))
		       return (Syn name)

-- | Create AND initialize a variable.
varinit :: CType -- ^ Type
           -> Syntax -> Syntax -> EasyEmit Syntax
varinit ty          
        (Syn name)  --  Name for the variable
        (Syn rhs)   --  RHS expression to provide the initial value for the  variable.
  = 
   do emitStmt (Syn (pPrint ty <+> name <+> "=" <+> rhs))
      return (Syn name)

-- A var declaration with a constructor invocation.
-- classvar :: Type -> Syntax -> [Syntax] -> EasyEmit Syntax
-- classvar ty (Syn name) args =
--    do emitStmt (Syn (pPrint ty <+> name <+> pcommasep (map fromSyntax args)))
--       return (Syn name)

-- Without names:
----------------------------------------
gensym :: Doc -> EasyEmit Syntax
gensym root = 
   do (ls,cnt) <- S.get
      S.put (ls,cnt+1)
      return$ Syn$ root <> int cnt

-- | Create a variable with an unspecified name (i.e. a temp variable).
tmpvar :: CType -> EasyEmit Syntax
tmpvar ty = do name <- gensym tmpPrefix
	       var ty name

-- | Create AND initialize a nameless variable.
tmpvarinit :: CType -> Syntax -> EasyEmit Syntax
tmpvarinit ty rhs = 
   do name <- gensym tmpPrefix
      varinit ty name rhs

tmpPrefix :: Doc
tmpPrefix = "eetmp"

vbraces d = lbrace $+$ d $+$ rbrace

-- A var declaration with a constructor invocation.
-- tmpclassvar :: CType -> [Syntax] -> EasyEmit Syntax
-- tmpclassvar ty args =
--    do name <- gensym "obj"
--       classvar ty name args


------------------------------------------------------------
-- C++ Statements 
------------------------------------------------------------

-- | This is a function in the meta language that represents a function
--   in the object language.
type ObjFun = ([Syntax] -> Syntax)

-- | Variable Assignment statement. @set x y@ is generates a semi-colon terminated line of code, e.g. @x = y;@
set :: Syntax -> Syntax -> EasyEmit ()
set (Syn x) (Syn v) = emitStmt$ Syn$ x <+> "=" <+> v 

-- Assignment for array locations:
arrset :: Syntax -> Syntax -> Syntax -> EasyEmit ()
arrset arr i rhs = set (arr `arrsub` i) rhs

-- Assignment for a field R.x.
fieldset :: Syntax -> Syntax -> Syntax -> EasyEmit ()
fieldset arr x rhs = set (arr `dot` x) rhs

-- | Function application as a complete statement.
appstmt :: ObjFun -> [Syntax] -> EasyEmit ()
appstmt fn ls = emitStmt$ fn ls

-- | Add-equals.  A shorthand that looks C-ish.
(+=) :: Syntax -> Syntax -> EasyEmit ()
(Syn x) += (Syn n) = emitStmt$ Syn$ x <+> "+=" <+> n

-- | Subtract-equals.  A shorthand that looks C-ish.
(-=) :: Syntax -> Syntax -> EasyEmit ()
(Syn x) -= (Syn n) = emitStmt$ Syn$ x <+> "-=" <+> n

-- | Emit comment line(s) in the output code.
comm :: String -> EasyEmit ()
comm x  = emitLine$ Syn$ txt
 where 
   txt = text$ maybeInit$ unlines lns -- init strips the last newline
   maybeInit [] = []
   maybeInit ls = init ls
   lns = map fn $ lines x --(render x)
   fn "" = ""
   fn other = "// " ++ other

-- | Conditionals at the statement level (@if@ / @else@).
if_ :: Syntax -> EasyEmit () -> EasyEmit () -> EasyEmit ()
if_ (Syn a) m1 m2 = 
  do let bod1 = execEasyEmit m1
	 bod2 = execEasyEmit m2
     emitLine$ Syn$ hangbraces ("if " <> PP.parens a) indent bod1
     emitLine$ Syn$ "else"
     emitLine$ Syn$ hangbraces (empty) indent bod2

-- | Return statements.     
return_ :: Syntax -> EasyEmit ()
return_ (Syn x) = emitStmt$ Syn$ "return " <> x


-- | C++ assert statements.
assert :: Syntax -> EasyEmit ()
assert (Syn exp) = 
 do emitStmt$ Syn ("assert" <> pcommasep [exp])

-- | For loop


------------------------------------------------------------
-- C++ Definitions & Declarations
------------------------------------------------------------

-- The funDef function creates a function definition as well as
-- returning a Haskell function that can be used to construct
-- applications of that function.
class FunDefable args where
  -- This is VERY painful, but need to expose separate keywords for pre- and post- the function name/args.
  funDefAttr :: String -> String -> CType -> String -> [CType] -> (args -> EasyEmit ()) -> EasyEmit ObjFun

instance FunDefable ()                            where funDefAttr pre post r n ts fn = funDefShared pre post r n ts fn (\ [] -> ())
instance FunDefable Syntax                        where funDefAttr pre post r n ts fn = funDefShared pre post r n ts fn (\ [a] -> a)        
instance FunDefable (Syntax,Syntax)               where funDefAttr pre post r n ts fn = funDefShared pre post r n ts fn (\ [a,b] -> (a,b))         
instance FunDefable (Syntax,Syntax,Syntax)        where funDefAttr pre post r n ts fn = funDefShared pre post r n ts fn (\ [a,b,c] -> (a,b,c))     
instance FunDefable (Syntax,Syntax,Syntax,Syntax) where funDefAttr pre post r n ts fn = funDefShared pre post r n ts fn (\ [a,b,c,d] -> (a,b,c,d)) 
instance FunDefable [Syntax]                      where funDefAttr pre post r n ts fn = funDefShared pre post r n ts fn id


-- | Define a C function.  Usage @funDef returnType name argTypes
--   funBody@.  The result of executing a `funDef` is BOTH to emit
--   code for the definition, and return a handle for calling the
--   function (without explicitly needing its name).
funDef       :: FunDefable args =>
                CType                 -- ^ Return type of function
             -> String                -- ^ Name of function.
             -> [CType]               -- ^ Argument types
             -> (args -> EasyEmit ()) -- ^ Body of function, HOAS
             -> EasyEmit ObjFun       
funDef       = funDefAttr "" ""

-- Terrible ugliness just to deal with those darn const qualifiers:
constFunDef  :: FunDefable args => CType -> String -> [CType] -> (args -> EasyEmit ()) -> EasyEmit ObjFun
constFunDef  = funDefAttr "" "const"

-- | Define a C function with inline attribute.
inlineFunDef :: FunDefable args => CType -> String -> [CType] -> (args -> EasyEmit ()) -> EasyEmit ObjFun
inlineFunDef = funDefAttr "inline" ""

-- Internal helper function used above:
funDefShared :: String -> String -> CType -> String -> [CType] -> (t1 -> EasyEmit a) -> ([Syntax] -> t1) -> EasyEmit ([Syntax] -> Syntax)
funDefShared pre postqualifiers retty name tyls fn formTup  = 
    do (ls,c) <- S.get 
       args <- sequence$ take (length tyls) (repeat$ gensym "arg") -- Generate temp names only (emit nothing).
       let body = execEasyEmit (fn$ formTup args)
	   formals = map (\ (ty,a) -> pPrint ty <+> fromSyntax a) (zip tyls args)
       emitLine$ Syn$ 
          hangbraces ((if pre P.== "" then empty else text (pre++" ")) <> 
		      pPrint retty <+> text name <> pcommasep formals <+> (text postqualifiers)) 
	             indent body
       return (\ args -> Syn$ text name <> (pcommasep (map fromSyntax args)))

-- | A function definition that does not use HOAS (higher-order
--   abstract-syntax), and instead expects explicit 
rawFunDef :: CType -> String -> [(CType,String)] -> EasyEmit () -> EasyEmit ObjFun
rawFunDef = rawFunDefShared False

-- | A variant of @rawFunDef@ that appends a prototype before the function definition.
rawFunDefProto :: CType -> String -> [(CType,String)] -> EasyEmit () -> EasyEmit ObjFun
rawFunDefProto = rawFunDefShared True

-- | A helper function that may or may not append a prototype.
rawFunDefShared :: Bool -> CType -> String -> [(CType,String)] -> EasyEmit () -> EasyEmit ObjFun
rawFunDefShared doProto retty name argls bod = do
   let body    = execEasyEmit bod
       formals = map (\ (ty,a) -> pPrint ty <+> text a) argls
       proto   = pPrint retty <+> text name <> pcommasep formals
   if doProto then emitStmt (toSyntax proto) else return ()
   emitLine$ Syn$ 
      hangbraces proto
                 indent body
   return (\ args -> Syn$ text name <> (pcommasep (map fromSyntax args)))


-- | This applies a C/C++ function referred to by name (defined elsewhere):
function :: Syntax -- ^ Name
         -> ObjFun
function (Syn name) = 
  \ args -> Syn$ name <> (pcommasep$ map fromSyntax args)

-- Shortcut for applying a method given an object or object reference.
methcall :: Syntax -> Syntax -> ObjFun
methcall obj meth args = obj `dot` (function meth args)

-- | For loop common case: for loop over a range with integer index:
-- Input is [Inclusive,Exclusive) range.
forRange :: (Syntax,Syntax) -> (Syntax -> EasyEmit ()) -> EasyEmit ()
forRange (start,end) = forStridedRange (start,1,end)

-- | Variant of `forRange` that also specifies the stride (increment on each loop iteration).
forStridedRange :: (Syntax,Syntax,Syntax) -> (Syntax -> EasyEmit ()) -> EasyEmit ()
forStridedRange (start,stride,end) fn = for start (<end) (+stride) fn

-- | Variant of `forRange` for parallel Cilk loops.
cilkForRange :: (Syntax,Syntax) -> (Syntax -> EasyEmit ()) -> EasyEmit ()
cilkForRange (start,end) = cilkForStridedRange (start,1,end)
  
-- | Variant of `forStridedRange` for parallel Cilk loops.
cilkForStridedRange :: (Syntax,Syntax,Syntax) -> (Syntax -> EasyEmit ()) -> EasyEmit ()
cilkForStridedRange (start,Syn stride,end) fn = do
  emitLine "#pragma vector always"
  emitLine "#pragma ivdep"
  rawFor "_Cilk_for" start (<end) (\ (Syn i) -> Syn$ i <+> "+=" <+> stride) fn


-- | General for loop with one iteration variable.  Three parameters
--   to the iteration: one value, and two functions.  Typical
--   arguments are @0@, @(<n)@, @(+1)@.  The body is the fourth
--   argument.
for :: Syntax -> (Syntax -> Syntax) -> (Syntax -> Syntax) -> (Syntax -> EasyEmit()) -> EasyEmit ()
for init test incr bodyFn =
  rawFor "for" init test (\ (Syn i) -> Syn (i <+> "=" <+> fromSyntax (incr (Syn i)))) bodyFn

-- | A general form of the for loop.  The for keyword is parametized and the
-- increment is expected to return a full assignment (including =, +=, etc).
rawFor :: Syntax -> Syntax -> (Syntax -> Syntax) -> (Syntax -> Syntax) -> (Syntax -> EasyEmit()) -> EasyEmit ()
rawFor (Syn forKeyword) init test incr bodyFn = 
  do Syn var <- gensym "i"
     (ls,oldcnt) <- S.get
     let (_,newcnt,body) = rawRunEasyEmit oldcnt $ bodyFn (Syn var)
     
     -- To maintain uniqueness we take the counter mods from the body.
     -- TODO: A cleaner way to do this would be to include the indent level in the state monad and NOT LEAVE IT.
     S.put (ls, newcnt)

     let s1 = t"int64_t" <+> var <+> "=" <+> fromSyntax init
         s2 = fromSyntax$ test (Syn var)
         s3 = (fromSyntax$ incr (Syn var))

     emitLine$ Syn$ hangbraces (forKeyword <+> PP.parens (s1 <> semi <+>
                                                          s2 <> semi <+>
                                                          s3)) indent $
	            body


-- Helper used below:
a <++> b | a P.== "" = b
a <++> b | b P.== "" = a
a <++> b             = a <+> b

-- This creates a class-decl-like pattern with a ':'
-- It is parameterized by a little prefix which could be "class" or "struct" or anything else.
-- Similarly, there's a postfix which is usually ";".
classLike :: String -> String -> Syntax -> Syntax -> EasyEmit () -> EasyEmit ()
classLike prefix postfix (Syn name) (Syn inherits) m = 
  do 
     putD$ t prefix <++> 
	   hsep (if inherits P.== empty
		 then [name]
		 else [name <+> colon, inherits])
     block m
     emitToPrevLine$ strToSyn postfix 

-- | Takes: name, inheritance expression, and a body.
cppClass :: Syntax -> Syntax -> EasyEmit () -> EasyEmit ()
cppClass = classLike "class" ";"

-- | Takes: name, inheritance expression, and a body.
cppStruct :: Syntax -> Syntax -> EasyEmit () -> EasyEmit ()
cppStruct = classLike "struct" ";"

-- Arg list is (type,argname) and init list is (name,expression/value)
cppConstructor :: Syntax -> [(CType,Syntax)] -> [(Syntax,Syntax)] -> EasyEmit () -> EasyEmit ()
cppConstructor (Syn name) args inits body = 
    let fn (t,x) = pPrint t <+> fromSyntax x in
    classLike "" "" (Syn$ name <> PP.parens (commasep$ map fn args)) 
		    (Syn$ commasep$ map (\ (a,b) -> fromSyntax a <> PP.parens (fromSyntax b)) inits)
	      body

-- Constructor method prototypes just look like applications
constructorPrototype :: Syntax -> [Syntax] -> EasyEmit ()
constructorPrototype name args = 
  appstmt (function name) args

-- | Run the provided code-emitting computation, and place its output
--   inside a Curly-brace delimited, indented block of statements.
block :: EasyEmit () -> EasyEmit ()
block m =
  -- POSSIBLY INEFFICIENT!
  -- TODO: Implement this by tracking the indent level in the monad:
  do let body = execEasyEmit m
     emitLine "{"
     emitLine$ Syn$ nest indent body
     emitLine "}"



----------------------------------------------------------------------------------------------------
-- Overloaded booleans and predicates from Lennart Augustsson:
----------------------------------------------------------------------------------------------------

-- | Generalization of the 'Bool' type.  Used by the generalized 'Eq' and 'Ord'.
class Boolean bool where
    (&&)  :: bool -> bool -> bool   -- ^Logical conjunction.
    (||)  :: bool -> bool -> bool   -- ^Logical disjunction.
    not   :: bool -> bool           -- ^Locical negation.
    false :: bool                   -- ^Truth.
    true  :: bool                   -- ^Falsity.
    fromBool :: Bool -> bool        -- ^Convert a 'Bool' to the generalized Boolean type.
    fromBool b = if b then true else false

-- Why not just make this part of the above class?
-- | Generalization of the @if@ construct.
--class (Boolean bool) => Conditional bool a where -- orig
--class (Boolean bool) => Conditional bool where
--    conditional :: bool -> a -> a -> a -- ^Pick the first argument if the 'Boolean' value is true, otherwise the second argument.


--class (Boolean bool) => Eq a bool {- x | a -> bool -} where
class (Boolean bool) => Eq a bool | a -> bool where
    (==) :: a -> a -> bool
    (/=) :: a -> a -> bool

    x /= y  =  not (x == y)
    x == y  =  not (x /= y)


--class (Conditional bool Ordering, Eq a bool) => Ord a bool | a -> bool where
--class (Conditional bool, Eq a bool) => Ord a bool | a -> bool where
class (Boolean bool, Eq a bool) => Ord a bool | a -> bool where
    (<), (<=), (>), (>=) :: a -> a -> bool
    max, min             :: a -> a -> a

-- Need to define precedence because these new operations really have nothing to do with the originals:
infix  4  ==, /=, <, <=, >=, >
infixr 3  &&
infixr 2  ||


----------------------------------------------------------------------------------------------------
-- Internal helpers:
----------------------------------------------------------------------------------------------------

-- Shorthand: I am very lazy.
t :: String -> Doc
t = text

-- Constant: indentation used for code generation.
indent :: Int
indent = 4

-- Braces-delimited as in C/C++/Java code.
hangbraces :: Doc -> Int -> Doc -> Doc
hangbraces d1 n d2 = sep [d1, vbraces$ nest n d2]

dubquotes :: SynChunk a => a -> Doc
dubquotes d = (t"\"") <> toDoc d <> (t"\"")

escapeString :: String -> String
escapeString = foldr showLitChar ""


-- This overloading just supports my laziness:
class SynChunk a where 
  toDoc :: a -> Doc
instance SynChunk String where 
  toDoc = text
instance SynChunk Doc where 
  toDoc = id

----------------------------------------------------------------------------------------------------
-- Testing:
----------------------------------------------------------------------------------------------------

t1 = cppClass "foo" "bar" $ comm "body"

{-
t2 = execEasyEmit$ funDef TInt "foo" [TInt] $ \(Syn y) -> 
       do comm "Body"
	  funDef TInt "nested" [] $ \ () -> comm "Inner body"
	  return ()


ee_example :: EasyEmit ()
ee_example = 
  do 
     comm "\nFirst some global vars:\n "
     y <- tmpvar TInt
     x <- var TInt "x"

     bar <- funDef (TSym "void") "bar" [TInt, TInt] $ \ (z,q) -> do
	 set y (z + q)

     comm "\nA function declaration:"
     foo <- funDef TInt "foo" [TInt] $ \y -> do
	 x += (x + y * 3)
	 x -= 4
	 ret x

     let baz  = function "baz"
	 quux = fromString "quux"

     app baz [quux, quux]

     forLoopSimple (0,10) $ \i -> do
	 if_ (i == 10 || i > 100)
	     (app foo [foo [i / 10]])
	     (app foo [i ? 3 .: 4])

   --   cppClass "blah" $ do 
   --       if_ (app f x) x x 
   -- --      funDef "method" [TInt, TFloat] $ \(y,z) -> y + z

ee_test1 = testCase "" "Code emission example"$ 
	   391 ~=? (length$ render$ execEasyEmit ee_example)

tests_easyemit = testSet "EasyEmit" [ee_test1]
-}

----------------------------------------------------------------------------------------------------
-- String Builder
----------------------------------------------------------------------------------------------------
-- We abstract the process of creating strings so that we can make our
-- code generation more efficient when we feel like it (later).
--
-- I couldn't find a nice simple version of this in hackage or the
-- standard libraries so here we roll our own (trivial) StringBuilder class.

-- NOTE: It would be nice to do all this with ByteString, but alas the
-- pretty printing infrastructure uses Strings.
class Monad m => StringBuilder m where 
  putS  :: String -> m ()
  putD  :: Doc -> m () 
  runSB :: m a -> (String, a)
  writeSB :: Handle -> m a -> IO a

  -- Default inefficient implementation:
  putS s = putD (text s)
  putD d = putS (show d)
  writeSB h m = let (s,a) = runSB m in  -- This appends the whole string... it shouldn't.
		do hPutStr h s
		   return a

type SimpleBuilder a = S.State [String] a

-- Here's something simple, not yet bothering with compact strings or file Handles, just
-- accumulating a list of strings.
--instance StringBuilder SimpleBuilder where 
instance StringBuilder (S.State [String]) where 
  putS s = S.modify (s:)
  runSB m = let (res,ls) = S.runState m [] 
	    in (concat$ reverse ls, res)

