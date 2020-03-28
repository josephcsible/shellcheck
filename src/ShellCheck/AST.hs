{-
    Copyright 2012-2019 Vidar Holen

    This file is part of ShellCheck.
    https://www.shellcheck.net

    ShellCheck is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    ShellCheck is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DeriveTraversable, TemplateHaskell, TypeFamilies #-}
module ShellCheck.AST where

import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import GHC.Generics (Generic)
import Control.Monad.Identity
import Control.DeepSeq
import Text.Parsec
import qualified ShellCheck.Regex as Re
import Prelude hiding (id)

newtype Id = Id Int deriving (Show, Eq, Ord, Generic, NFData)

data Quoted = Quoted | Unquoted deriving (Show, Eq)
data Dashed = Dashed | Undashed deriving (Show, Eq)
data AssignmentMode = Assign | Append deriving (Show, Eq)
newtype FunctionKeyword = FunctionKeyword Bool deriving (Show, Eq)
newtype FunctionParentheses = FunctionParentheses Bool deriving (Show, Eq)
data CaseType = CaseBreak | CaseFallThrough | CaseContinue deriving (Show, Eq)

newtype Root = Root Token
data Token =
    TA_Binary Id String Token Token
    | TA_Assignment Id String Token Token
    | TA_Variable Id String [Token]
    | TA_Expansion Id [Token]
    | TA_Sequence Id [Token]
    | TA_Trinary Id Token Token Token
    | TA_Unary Id String Token
    | TC_And Id ConditionType String Token Token
    | TC_Binary Id ConditionType String Token Token
    | TC_Group Id ConditionType Token
    | TC_Nullary Id ConditionType Token
    | TC_Or Id ConditionType String Token Token
    | TC_Unary Id ConditionType String Token
    | TC_Empty Id ConditionType
    | T_AND_IF Id
    | T_AndIf Id Token Token
    | T_Arithmetic Id Token
    | T_Array Id [Token]
    | T_IndexedElement Id [Token] Token
    -- Store the index as string, and parse as arithmetic or string later
    | T_UnparsedIndex Id SourcePos String
    | T_Assignment Id AssignmentMode String [Token] Token
    | T_Backgrounded Id Token
    | T_Backticked Id [Token]
    | T_Bang Id
    | T_Banged Id Token
    | T_BraceExpansion Id [Token]
    | T_BraceGroup Id [Token]
    | T_CLOBBER Id
    | T_Case Id
    | T_CaseExpression Id Token [(CaseType, [Token], [Token])]
    | T_Condition Id ConditionType Token
    | T_DGREAT Id
    | T_DLESS Id
    | T_DLESSDASH Id
    | T_DSEMI Id
    | T_Do Id
    | T_DollarArithmetic Id Token
    | T_DollarBraced Id Bool Token
    | T_DollarBracket Id Token
    | T_DollarDoubleQuoted Id [Token]
    | T_DollarExpansion Id [Token]
    | T_DollarSingleQuoted Id String
    | T_DollarBraceCommandExpansion Id [Token]
    | T_Done Id
    | T_DoubleQuoted Id [Token]
    | T_EOF Id
    | T_Elif Id
    | T_Else Id
    | T_Esac Id
    | T_Extglob Id String [Token]
    | T_FdRedirect Id String Token
    | T_Fi Id
    | T_For Id
    | T_ForArithmetic Id Token Token Token [Token]
    | T_ForIn Id String [Token] [Token]
    | T_Function Id FunctionKeyword FunctionParentheses String Token
    | T_GREATAND Id
    | T_Glob Id String
    | T_Greater Id
    | T_HereDoc Id Dashed Quoted String [Token]
    | T_HereString Id Token
    | T_If Id
    | T_IfExpression Id [([Token],[Token])] [Token]
    | T_In  Id
    | T_IoFile Id Token Token
    | T_IoDuplicate Id Token String
    | T_LESSAND Id
    | T_LESSGREAT Id
    | T_Lbrace Id
    | T_Less Id
    | T_Literal Id String
    | T_Lparen Id
    | T_NEWLINE Id
    | T_NormalWord Id [Token]
    | T_OR_IF Id
    | T_OrIf Id Token Token
    | T_ParamSubSpecialChar Id String -- e.g. '%' in ${foo%bar}  or '/' in ${foo/bar/baz}
    | T_Pipeline Id [Token] [Token] -- [Pipe separators] [Commands]
    | T_ProcSub Id String [Token]
    | T_Rbrace Id
    | T_Redirecting Id [Token] Token
    | T_Rparen Id
    | T_Script Id Token [Token] -- Shebang T_Literal, followed by script.
    | T_Select Id
    | T_SelectIn Id String [Token] [Token]
    | T_Semi Id
    | T_SimpleCommand Id [Token] [Token]
    | T_SingleQuoted Id String
    | T_Subshell Id [Token]
    | T_Then Id
    | T_Until Id
    | T_UntilExpression Id [Token] [Token]
    | T_While Id
    | T_WhileExpression Id [Token] [Token]
    | T_Annotation Id [Annotation] Token
    | T_Pipe Id String
    | T_CoProc Id (Maybe String) Token
    | T_CoProcBody Id Token
    | T_Include Id Token
    | T_SourceCommand Id Token Token
    | T_BatsTest Id Token Token
    deriving (Show)

data Annotation =
    DisableComment Integer
    | EnableComment String
    | SourceOverride String
    | ShellOverride String
    | SourcePath String
    deriving (Show, Eq)
data ConditionType = DoubleBracket | SingleBracket deriving (Show, Eq)

makeBaseFunctor ''Token

-- This is an abomination.
tokenEquals :: Token -> Token -> Bool
tokenEquals a b = kludge a == kludge b
    where kludge s = Re.subRegex (Re.mkRegex "\\(Id [0-9]+\\)") (show s) "(Id 0)"

instance Eq Token where
    (==) = tokenEquals

analyze :: Monad m => (Token -> m ()) -> (Token -> m ()) -> (Token -> m Token) -> Token -> m Token
analyze f g i =
    round
  where
    round t = do
        f t
        newT <- fmap embed . traverse round . project $ t
        g t
        i newT

getId :: Token -> Id
getId t = case t of
        T_AND_IF id  -> id
        T_OR_IF id  -> id
        T_DSEMI id  -> id
        T_Semi id  -> id
        T_DLESS id  -> id
        T_DGREAT id  -> id
        T_LESSAND id  -> id
        T_GREATAND id  -> id
        T_LESSGREAT id  -> id
        T_DLESSDASH id  -> id
        T_CLOBBER id  -> id
        T_If id  -> id
        T_Then id  -> id
        T_Else id  -> id
        T_Elif id  -> id
        T_Fi id  -> id
        T_Do id  -> id
        T_Done id  -> id
        T_Case id  -> id
        T_Esac id  -> id
        T_While id  -> id
        T_Until id  -> id
        T_For id  -> id
        T_Select id  -> id
        T_Lbrace id  -> id
        T_Rbrace id  -> id
        T_Lparen id  -> id
        T_Rparen id  -> id
        T_Bang id  -> id
        T_In  id  -> id
        T_NEWLINE id  -> id
        T_EOF id  -> id
        T_Less id  -> id
        T_Greater id  -> id
        T_SingleQuoted id _  -> id
        T_Literal id _  -> id
        T_NormalWord id _  -> id
        T_DoubleQuoted id _  -> id
        T_DollarExpansion id _  -> id
        T_DollarBraced id _ _ -> id
        T_DollarArithmetic id _  -> id
        T_BraceExpansion id _  -> id
        T_ParamSubSpecialChar id _ -> id
        T_DollarBraceCommandExpansion id _  -> id
        T_IoFile id _ _  -> id
        T_IoDuplicate id _ _  -> id
        T_HereDoc id _ _ _ _ -> id
        T_HereString id _  -> id
        T_FdRedirect id _ _  -> id
        T_Assignment id _ _ _ _  -> id
        T_Array id _  -> id
        T_IndexedElement id _ _  -> id
        T_Redirecting id _ _  -> id
        T_SimpleCommand id _ _  -> id
        T_Pipeline id _ _  -> id
        T_Banged id _  -> id
        T_AndIf id _ _ -> id
        T_OrIf id _ _ -> id
        T_Backgrounded id _  -> id
        T_IfExpression id _ _  -> id
        T_Subshell id _  -> id
        T_BraceGroup id _  -> id
        T_WhileExpression id _ _  -> id
        T_UntilExpression id _ _  -> id
        T_ForIn id _ _ _  -> id
        T_SelectIn id _ _ _  -> id
        T_CaseExpression id _ _ -> id
        T_Function id _ _ _ _  -> id
        T_Arithmetic id _  -> id
        T_Script id _ _  -> id
        T_Condition id _ _  -> id
        T_Extglob id _ _ -> id
        T_Backticked id _ -> id
        TC_And id _ _ _ _  -> id
        TC_Or id _ _ _ _  -> id
        TC_Group id _ _  -> id
        TC_Binary id _ _ _ _  -> id
        TC_Unary id _ _ _  -> id
        TC_Nullary id _ _  -> id
        TA_Binary id _ _ _  -> id
        TA_Assignment id _ _ _  -> id
        TA_Unary id _ _  -> id
        TA_Sequence id _  -> id
        TA_Trinary id _ _ _  -> id
        TA_Expansion id _  -> id
        T_ProcSub id _ _ -> id
        T_Glob id _ -> id
        T_ForArithmetic id _ _ _ _ -> id
        T_DollarSingleQuoted id _ -> id
        T_DollarDoubleQuoted id _ -> id
        T_DollarBracket id _ -> id
        T_Annotation id _ _ -> id
        T_Pipe id _ -> id
        T_CoProc id _ _ -> id
        T_CoProcBody id _ -> id
        T_Include id _ -> id
        T_SourceCommand id _ _ -> id
        T_UnparsedIndex id _ _ -> id
        TC_Empty id _ -> id
        TA_Variable id _ _ -> id
        T_BatsTest id _ _ -> id

blank :: Monad m => Token -> m ()
blank = const $ return ()
doAnalysis :: Monad m => (Token -> m ()) -> Token -> m Token
doAnalysis f = analyze f blank return
doStackAnalysis :: Monad m => (Token -> m ()) -> (Token -> m ()) -> Token -> m Token
doStackAnalysis startToken endToken = analyze startToken endToken return
doTransform :: (Token -> Token) -> Token -> Token
doTransform i = runIdentity . analyze blank blank (return . i)

