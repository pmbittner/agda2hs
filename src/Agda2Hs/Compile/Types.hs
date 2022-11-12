module Agda2Hs.Compile.Types where

import Control.Monad.Reader ( ReaderT )
import Control.Monad.Writer ( WriterT )
import Control.DeepSeq ( NFData(..) )

import Data.Set ( Set )

import qualified Language.Haskell.Exts.SrcLoc as Hs
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Extension as Hs
import qualified Language.Haskell.Exts.Comments as Hs

import Agda.Compiler.Backend ( Definition, QName, ModuleName, TCM )
import Agda.Syntax.Position ( Range )
import Agda.Syntax.TopLevelModuleName ( TopLevelModuleName )

import Agda2Hs.HsUtils ( Strictness )

type ModuleEnv   = TopLevelModuleName
type ModuleRes   = ()
type CompiledDef = [Ranged [Hs.Decl ()]]
type Ranged a    = (Range, a)

type Code = (Hs.Module Hs.SrcSpanInfo, [Hs.Comment])

data Options = Options { optOutDir     :: FilePath,
                         optExtensions :: [Hs.Extension] }

-- Required by Agda-2.6.2, but we don't really care.
instance NFData Options where
  rnf _ = ()

data CompileEnv = CompileEnv
  { minRecordName :: Maybe ModuleName
  -- ^ keeps track of the current minimal record we are compiling
  , locals :: LocalDecls
  -- ^ keeps track of the current clause's where declarations
  , isCompilingInstance :: Bool
  }

type Import = (Hs.ModuleName (), Hs.QName ())
type Imports = [Import]

type C = ReaderT CompileEnv (WriterT Imports TCM)

-- Currently we can compile an Agda "Dom Type" in three ways:
-- - To a type in Haskell (with perhaps a strictness annotation)
-- - To a typeclass constraint in Haskell
-- - To nothing (e.g. for proofs)
data CompiledDom
  = DomType Strictness (Hs.Type ())
  | DomConstraint (Hs.Asst ())
  | DomDropped

type LocalDecls = [QName]

data RecordTarget = ToRecord [Hs.Deriving ()] | ToClass [String]
