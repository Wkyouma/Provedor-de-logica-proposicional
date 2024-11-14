import Data.List (isPrefixOf, nub)
--tipos de tokens
data Token
  = Var Char
  | Boolean Bool
  | Not
  | And
  | Or
  | Implication
  | Biconditional
  | LeftParen
  | RightParen
  deriving (Show, Eq)

-- Função para transformar em token
tokenize  :: String -> [Token]
tokenize  [] = []
tokenize  x
  | "(" `isPrefixOf` x = LeftParen : tokenize  (drop 1 x)
  | ")" `isPrefixOf` x = RightParen : tokenize  (drop 1 x)
  | "v" `isPrefixOf` x || "∨" `isPrefixOf` x = Or : tokenize  (drop 1 x)
  | "ou" `isPrefixOf` x || "or" `isPrefixOf` x = Or : tokenize  (drop 2 x)
  | "\\lor" `isPrefixOf` x = Or : tokenize  (drop 4 x)
  | "^" `isPrefixOf` x || "∧" `isPrefixOf` x = And : tokenize  (drop 1 x)
  | "e" `isPrefixOf` x || "and" `isPrefixOf` x = And : tokenize  (drop 3 x)
  | "\\land" `isPrefixOf` x = And : tokenize  (drop 5 x)
  | "~" `isPrefixOf` x || "¬" `isPrefixOf` x = Not : tokenize  (drop 1 x)
  | "not" `isPrefixOf` x = Not : tokenize  (drop 3 x)
  | "\\neg" `isPrefixOf` x = Not : tokenize  (drop 4 x)
  | "¬" `isPrefixOf` x = Not : tokenize  (drop 1 x)
  | "->" `isPrefixOf` x || "=>" `isPrefixOf` x = Implication : tokenize  (drop 2 x)
  | "→" `isPrefixOf` x = Implication : tokenize  (drop 1 x)
  | "\\to" `isPrefixOf` x = Implication : tokenize  (drop 3 x)
  | "<->" `isPrefixOf` x || "<=>" `isPrefixOf` x = Biconditional : tokenize  (drop 3 x)
  | "↔" `isPrefixOf` x = Biconditional : tokenize  (drop 1 x)
  | "\\iff" `isPrefixOf` x = Biconditional : tokenize  (drop 4 x)
  | "true" `isPrefixOf` x = Boolean True : tokenize  (drop 4 x)
  | "false" `isPrefixOf` x = Boolean False : tokenize  (drop 5 x)
  | head x `elem` ['A' .. 'Z'] = Var (head x) : tokenize  (drop 1 x)
  | head x == ' ' || head x == '\t' = tokenize  (drop 1 x)
  | otherwise = error $ "Caractere inválido: " ++ [head x]

-- Tipo de dado para representar expressões proposicionais
data Proposicao
  = PropVar Char
  | PropBool Bool
  | PropNot Proposicao
  | PropAnd Proposicao Proposicao
  | PropOr Proposicao Proposicao
  | PropImpl Proposicao Proposicao
  | PropBic Proposicao Proposicao
  deriving (Eq, Show)

-- Função para analisar sintaticamente a lista de tokens em uma Proposicao
parseExpr :: [Token] -> (Proposicao, [Token])
parseExpr tokens = parseBiconditional tokens

parseBiconditional :: [Token] -> (Proposicao, [Token])
parseBiconditional tokens = 
    let (left, tokens1) = parseImplication tokens
    in case tokens1 of
        (Biconditional : rest) -> 
            let (right, tokens2) = parseBiconditional rest
            in (PropBic left right, tokens2)
        _ -> (left, tokens1)

parseImplication :: [Token] -> (Proposicao, [Token])
parseImplication tokens = 
    let (left, tokens1) = parseOr tokens
    in case tokens1 of
        (Implication : rest) ->
            let (right, tokens2) = parseImplication rest
            in (PropImpl left right, tokens2)
        _ -> (left, tokens1)

parseOr :: [Token] -> (Proposicao, [Token])
parseOr tokens = 
    let (left, tokens1) = parseAnd tokens
    in case tokens1 of
        (Or : rest) ->
            let (right, tokens2) = parseOr rest
            in (PropOr left right, tokens2)
        _ -> (left, tokens1)

parseAnd :: [Token] -> (Proposicao, [Token])
parseAnd tokens =
    let (left, tokens1) = parseNot tokens
    in case tokens1 of
        (And : rest) ->
            let (right, tokens2) = parseAnd rest
            in (PropAnd left right, tokens2)
        _ -> (left, tokens1)

parseNot :: [Token] -> (Proposicao, [Token])
parseNot tokens =
    case tokens of
        (Not : rest) ->
            let (expr, tokens1) = parseNot rest
            in (PropNot expr, tokens1)
        _ -> parsePrimary tokens

parsePrimary :: [Token] -> (Proposicao, [Token])
parsePrimary tokens =
    case tokens of
        (Var v : rest) -> (PropVar v, rest)
        (Boolean b : rest) -> (PropBool b, rest)
        (LeftParen : rest) ->
            let (expr, tokens1) = parseExpr rest
            in case tokens1 of
                (RightParen : rest1) -> (expr, rest1)
                _ -> error "Esperado parêntese de fechamento"
        _ -> error "Token inesperado"

-- Classificação de uma expressão como Tautologia, Contradição ou Contingente
classificar :: Proposicao -> String
classificar expr =
  let resultados = avaliarExpressao expr
  in if all id resultados then "Tautologia"
     else if not (any id resultados) then "Contradição"
     else "Contingente"

-- Avaliação da expressão para todas as combinações de valores booleanos das variáveis
avaliarExpressao :: Proposicao -> [Bool]
avaliarExpressao expr =
  let vars = variaveisProp expr
      combinacoes = sequence (replicate (length vars) [True, False])
  in [evalProposicao (zip vars c) expr | c <- combinacoes]

-- Função para extrair variáveis de uma Proposicao
variaveisProp :: Proposicao -> [Char]
variaveisProp p = nub (vars p)
  where
    vars (PropVar x) = [x]
    vars (PropBool _) = []
    vars (PropNot x) = vars x
    vars (PropAnd x y) = vars x ++ vars y
    vars (PropOr x y) = vars x ++ vars y
    vars (PropImpl x y) = vars x ++ vars y
    vars (PropBic x y) = vars x ++ vars y

-- Função para avaliar uma Proposicao dada uma atribuição de valores
evalProposicao :: [(Char, Bool)] -> Proposicao -> Bool
evalProposicao vars (PropVar x) =
    case lookup x vars of
        Just val -> val
        Nothing -> error $ "Variável não encontrada: " ++ [x]
evalProposicao _ (PropBool b) = b
evalProposicao vars (PropNot x) = not (evalProposicao vars x)
evalProposicao vars (PropAnd x y) = evalProposicao vars x && evalProposicao vars y
evalProposicao vars (PropOr x y) = evalProposicao vars x || evalProposicao vars y
evalProposicao vars (PropImpl x y) = not (evalProposicao vars x) || evalProposicao vars y
evalProposicao vars (PropBic x y) = evalProposicao vars x == evalProposicao vars y

-- Eliminar implicações e bicondicionais
transImplic :: Proposicao -> Proposicao
transImplic (PropVar x) = PropVar x
transImplic (PropBool b) = PropBool b
transImplic (PropNot x) = PropNot (transImplic x)
transImplic (PropAnd x y) = PropAnd (transImplic x) (transImplic y)
transImplic (PropOr x y) = PropOr (transImplic x) (transImplic y)
transImplic (PropImpl x y) = PropOr (PropNot (transImplic x)) (transImplic y)
transImplic (PropBic x y) = PropAnd (transImplic (PropImpl x y)) (transImplic (PropImpl y x))

-- Mover negações para dentro e simplificar dupla negação
transNeg :: Proposicao -> Proposicao
transNeg (PropVar x) = PropVar x
transNeg (PropBool b) = PropBool b
transNeg (PropNot (PropNot x)) = transNeg x  -- Elimina dupla negação
transNeg (PropNot (PropAnd x y)) = PropOr (transNeg (PropNot x)) (transNeg (PropNot y))  -- De Morgan
transNeg (PropNot (PropOr x y)) = PropAnd (transNeg (PropNot x)) (transNeg (PropNot y))  -- De Morgan
transNeg (PropNot x) = PropNot (transNeg x)
transNeg (PropAnd x y) = PropAnd (transNeg x) (transNeg y)
transNeg (PropOr x y) = PropOr (transNeg x) (transNeg y)
transNeg x = x  -- Caso base para outras formas

-- Distribuir disjunções sobre conjunções para obter a FNC
distributivaProp :: Proposicao -> Proposicao
distributivaProp p =
  let p' = distribDisj p
  in if p == p' then p else distributivaProp p'

-- Distribuição parcial das disjunções sobre conjunções
distribDisj :: Proposicao -> Proposicao
distribDisj (PropAnd x y) = PropAnd (distribDisj x) (distribDisj y)
distribDisj (PropOr (PropAnd x y) z) = PropAnd (distribDisj (PropOr x z)) (distribDisj (PropOr y z))
distribDisj (PropOr z (PropAnd x y)) = PropAnd (distribDisj (PropOr z x)) (distribDisj (PropOr z y))
distribDisj (PropOr x y) = PropOr (distribDisj x) (distribDisj y)
distribDisj (PropNot x) = PropNot (distribDisj x)
distribDisj x = x

-- Função principal para converter uma expressão para FNC
converterParaFNC :: Proposicao -> Proposicao
converterParaFNC = distributivaProp . transNeg . transImplic

-- Função para verificar se uma disjunção é uma cláusula de Horn
posiClausulaHorn :: Proposicao -> Bool
posiClausulaHorn (PropOr x y) = numPosi (PropOr x y) <= 1
posiClausulaHorn (PropVar _) = True  -- Um único literal é sempre uma cláusula de Horn
posiClausulaHorn (PropNot _) = True  -- Literal negado é aceitável
posiClausulaHorn _ = False

-- Contagem de literais positivos em uma expressão
numPosi :: Proposicao -> Int
numPosi (PropVar _) = 1
numPosi (PropNot _) = 0
numPosi (PropOr x y) = numPosi x + numPosi y
numPosi _ = 0

-- Separar as cláusulas da FNC
extrairClausulas :: Proposicao -> [Proposicao]
extrairClausulas (PropAnd x y) = extrairClausulas x ++ extrairClausulas y
extrairClausulas clausula = [clausula]

-- Exibir as cláusulas de Horn ou informar se não for possível
exibirClausulasHorn :: Proposicao -> IO ()
exibirClausulasHorn fnc = 
  let clausulas = extrairClausulas fnc
      clausulasHorn = filter posiClausulaHorn clausulas
  in if length clausulas == length clausulasHorn
     then do
       putStrLn "As cláusulas de Horn resultantes são:"
       mapM_ print clausulasHorn
     else
       putStrLn "A expressão não pode ser representada apenas com cláusulas de Horn."

printSeparator :: Char -> Int -> IO ()
printSeparator c n = putStrLn (replicate n c)

-- Função auxiliar para converter expressão Proposicao para LaTeX e terminal
toLatex :: Proposicao -> String
toLatex (PropVar x) = [x]
toLatex (PropBool True) = "true"
toLatex (PropBool False) = "false"
toLatex (PropNot x) = "\\neg " ++ toLatex x
toLatex (PropAnd x y) = "(" ++ toLatex x ++ " \\land " ++ toLatex y ++ ")"
toLatex (PropOr x y) = "(" ++ toLatex x ++ " \\lor " ++ toLatex y ++ ")"
toLatex (PropImpl x y) = "(" ++ toLatex x ++ " \\to " ++ toLatex y ++ ")"
toLatex (PropBic x y) = "(" ++ toLatex x ++ " \\leftrightarrow " ++ toLatex y ++ ")"

-- Função para exibir a expressão em LaTeX e no terminal
printLaTeX :: String -> Proposicao -> IO ()
printLaTeX msg expr = do
    putStrLn $ msg ++ " (Terminal): " ++ show expr
    putStrLn $ msg ++ " (LaTeX): $$" ++ toLatex expr ++ "$$"

main :: IO ()
main = do
    putStrLn "\n┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓"
    putStrLn "┃          📝 Entradas Aceitas             ┃"
    putStrLn "┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛"
    putStrLn ""
    putStrLn "  🔵  Parênteses:                         "
    putStrLn "    ➤ (     - Parêntese esquerdo        "
    putStrLn "    ➤ )     - Parêntese direito         "
    putStrLn ""
    putStrLn "  🔵 Operadores Lógicos:                "
    putStrLn "    ➤ v, ∨  - Operador OR              "
    putStrLn "    ➤ ou, or, \\lor  - Operador OR     "
    putStrLn "    ➤ ^, ∧  - Operador AND             "
    putStrLn "    ➤ e, and, \\land  - Operador AND   "
    putStrLn "    ➤ ~, ¬, not, \\neg  - Operador NOT "
    putStrLn "    ➤ ->, =>, \\to  - Implicação       "
    putStrLn "    ➤ →     - Implicação               "
    putStrLn "    ➤ <->, <=>, \\iff  - Bicondicional "
    putStrLn "    ➤ ↔     - Bicondicional            "
    putStrLn ""
    putStrLn "  🔵  Variáveis:                         "
    putStrLn "    ➤ [A-Z] - Variáveis (ex.: A, B, C, ...)"
    putStrLn ""
    putStrLn "  ⚠️ Observações:                      "
    putStrLn "    ➤ Espaços em branco e tabulações são ignorados"
    putStrLn "    ➤ Qualquer outro caractere resultará em erro"
    putStrLn "\nPor favor, insira a expressão lógica:"
    str <- getLine
    let tokenizado = tokenize  str
    putStrLn $ "Tokens: " ++ show tokenizado
    printSeparator '=' 100
    let (prop, restTokens) = parseExpr tokenizado
    if not (null restTokens)
        then error "Falha ao analisar toda a expressão"
        else do
            putStrLn $ "Expressão analisada: " ++ show prop
            putStrLn $ "Classificação da expressão: " ++ classificar prop
    printSeparator '=' 100
    printLaTeX "Expressão Proposicional" prop
    let fnc = converterParaFNC prop
    printLaTeX "Expressão em FNC" fnc
    printSeparator '=' 100
    exibirClausulasHorn fnc
