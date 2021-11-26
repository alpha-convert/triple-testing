{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}

module Parser where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Data.List

import Syntax

languageDef =
  emptyDef
    { Token.commentStart = "/*",
      Token.commentEnd = "*/",
      Token.commentLine = "//",
      Token.identStart = letter,
      Token.identLetter = alphaNum,
      Token.reservedNames =
        [ "if",
          "then",
          "else",
          "while",
          "do",
          "skip",
          "true",
          "false",
          "method",
          "int",
          "bool",
          "array",
          "return",
          "forall",
          "ensures",
          "requires",
          "returns"
        ],
      Token.reservedOpNames =
        [ "+",
          "-",
          "*",
          "/",
          ":=",
          "==",
          "!=",
          "%",
          "<",
          ">",
          ">=",
          "<=",
          "||",
          "&&",
          "!",
          ".len"
        ]
    }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer -- parses an identifier

reserved = Token.reserved lexer -- parses a reserved name

reservedOp = Token.reservedOp lexer -- parses an operator

parens = Token.parens lexer -- parses surrounding parenthesis:

brackets = Token.brackets lexer

braces = Token.braces lexer

integer = Token.integer lexer -- parses an integer

semi = Token.semi lexer -- parses a semicolon

whiteSpace = Token.whiteSpace lexer -- parses whitespace

boolLit :: Parser Lit
boolLit = (reserved "true" >> return (LBool True)) <|> (reserved "false" >> return (LBool False))

intLit :: Parser Lit
intLit = LInt . fromIntegral <$> integer

-- arrayLit :: Parser Lit
-- arrayLit = LArray <$> brackets (sepBy lit (optional whiteSpace >> char ','))

unitLit = char '(' >> char ')' >> return LUnit

lit :: Parser Lit
lit = unitLit <|> intLit <|> boolLit {-<|> arrayLit-}

lvalue :: Parser LVal
lvalue = LVar <$> identifier

  -- idx <- optionMaybe (brackets expr)
  -- return $ case idx of
    -- Nothing -> LVar x
    -- Just e -> LIndex x e

command :: Parser Cmd
command = parens command <|> sequenceOfCmd

sequenceOfCmd =
  do
    list <- sepBy1 command' semi
    return $ if length list == 1 then head list else Seq list

command' :: Parser Cmd
command' = ifCmd <|> whileCmd <|> skipCmd <|> assignCmd <|> returnCmd

ifCmd :: Parser Cmd
ifCmd =
  do
    reserved "if"
    cond <- expr
    reserved "then"
    stmt1 <- command
    reserved "else"
    IfElse cond stmt1 <$> command

whileCmd :: Parser Cmd
whileCmd =
  do
    reserved "while"
    cond <- expr
    body <- braces command
    return $ While cond body

assignCmd :: Parser Cmd
assignCmd =
  do
    lv <- lvalue
    reservedOp ":="
    Assign lv <$> expr

skipCmd :: Parser Cmd
skipCmd = reserved "skip" >> return Skip

returnCmd :: Parser Cmd
returnCmd = reserved "return" >> Return <$> expr


ops =
  [ [ Prefix (reservedOp "-" >> return (EMonOp MNeg)),
      Postfix (reservedOp ".len" >> return (EMonOp MNeg)),
      Infix (reservedOp "!!" >> return (EBinOp BIndex)) AssocLeft
    ],
    [ Infix (reservedOp "*" >> return (EBinOp BTimes)) AssocLeft,
      Infix (reservedOp "%" >> return (EBinOp BMod)) AssocLeft,
      Infix (reservedOp "/" >> return (EBinOp BDiv)) AssocLeft
    ],
    [ Infix (reservedOp "+" >> return (EBinOp BPlus)) AssocLeft,
      Infix (reservedOp "-" >> return (EBinOp BMinus)) AssocLeft
    ],
    [ Infix (reservedOp ">" >> return (EBinOp BGt)) AssocLeft,
      Infix (reservedOp "<" >> return (EBinOp BLt)) AssocLeft,
      Infix (reservedOp "<=" >> return (EBinOp BLeq)) AssocLeft,
      Infix (reservedOp ">=" >> return (EBinOp BGeq)) AssocLeft,
      Infix (reservedOp "==" >> return (EBinOp BEq)) AssocLeft,
      Infix (reservedOp "!=" >> return (EBinOp BNeq)) AssocLeft
    ],
    [ Prefix (reservedOp "!" >> return (EMonOp MNot)),
      Infix (reservedOp "&&" >> return (EBinOp BAnd)) AssocLeft,
      Infix (reservedOp "||" >> return (EBinOp BOr)) AssocLeft
    ]
  ]

expr' :: Parser Expr
expr' =
  parens expr
    <|> fmap EVar identifier
    <|> fmap ELit lit

expr :: Parser Expr
expr = buildExpressionParser ops expr'

typ :: Parser Typ
typ = (reserved "int" >> return TyInt) <|>
      (reserved "bool" >> return TyBool) <|>
      (reserved "unit" >> return TyUnit) <|>
      (reserved "array" >> TyArr <$> parens typ)

argList :: Parser [(Var,Typ)]
argList = argPair `sepBy1` (whiteSpace >> char ',' >> whiteSpace)
  where
    argPair = do
      x <- identifier
      reservedOp ":"
      t <- typ
      return (x,t)

numExpOps =
  [
    [ Prefix (reservedOp "-" >> return (NEMonOp NENeg))],
    [ Infix (reservedOp "*" >> return (NEBinOp NETimes)) AssocLeft{-,
      Infix (reservedOp "%" >> return (NEBinOp NEMod)) AssocLeft,
      Infix (reservedOp "/" >> return (NEBinOp NEDiv)) AssocLeft
      -}
    ],
    [ Infix (reservedOp "+" >> return (NEBinOp NEPlus)) AssocLeft,
      Infix (reservedOp "-" >> return (NEBinOp NEMinus)) AssocLeft
    ]
  ]

numExp' :: Parser NumExp
numExp' =
  parens numExp'
    <|> fmap NEVar identifier
    <|> fmap NEInt (fromInteger <$> integer)

numExp :: Parser NumExp
numExp = buildExpressionParser numExpOps numExp'

propOps =
  [
    [ Prefix (reservedOp "!" >> return (PMO PNot)),
      Infix (reservedOp "&&" >> return (PBO PAnd)) AssocLeft,
      Infix (reservedOp "||" >> return (PBO POr)) AssocLeft
    ]
  ]

propRel :: Parser PropRel
propRel = (reservedOp "<=" >> return RLeq)
        <|> (reservedOp ">=" >> return RGeq)
        <|> (reservedOp "<" >> return RLt)
        <|> (reservedOp ">" >> return RGt)
        <|> (reservedOp "==" >> return REq)
        <|> (reservedOp "!=" >> return RNeq)

propRelExp :: Parser Prop
propRelExp = do
    e1 <- numExp
    optional whiteSpace
    r <- propRel
    optional whiteSpace
    RelExp r e1 <$> numExp


prop' :: Parser Prop
prop' = parens prop'
    <|> propRelExp
    {- This might parse wrong... If we see a var, we're automatically assuming that it's
       a numerical var, and then trying a prop var if that fails...-}
    {-<|> fmap PropVar identifier-}

prop :: Parser Prop
prop = buildExpressionParser propOps prop'

pre :: Parser (Prop,Bool)
pre = reserved "requires" >> (,True) <$> prop

post :: Parser (Prop,Bool)
post = reserved "ensures" >> (,False) <$> prop

prePost :: Parser ([Prop],[Prop])
prePost = do
  conds <- sepBy (pre <|> post) whiteSpace
  let (pres,posts) = partition snd conds
  return (map fst pres, map fst posts)


{-type Method = {name :: String, args :: [(Var,Typ)], retTy :: Typ, body :: Cmd}-}
method :: Parser Method
method = do
  reserved "method"
  name <- identifier
  optional whiteSpace
  args <- parens argList
  optional whiteSpace
  reserved "returns"
  retName <- identifier
  char ':'
  optional whiteSpace
  retTy <- typ
  (pres,posts) <- prePost
  body <- braces command
  return $ Method {name,args,retTy,body,posts,pres,retName}

parseFile :: Parser a -> String -> IO a
parseFile p file =
  do
    program <- readFile file
    case parse (whiteSpace >> p) "" program of
      Left e -> print e >> fail "parse error"
      Right r -> return r

