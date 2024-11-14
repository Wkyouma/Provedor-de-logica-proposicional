
--tipos de tokens
data Token
  = Var Char
  | Booleano Bool
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
  | "(" `prefixOf` x = LeftParen : tokenize  (drop 1 x)
  | ")" `prefixOf` x = RightParen : tokenize  (drop 1 x)
  | "v" `prefixOf` x || "∨" `prefixOf` x = Or : tokenize  (drop 1 x)
  | "ou" `prefixOf` x || "or" `prefixOf` x = Or : tokenize  (drop 2 x)
  | "\\lor" `prefixOf` x = Or : tokenize  (drop 4 x)
  | "^" `prefixOf` x || "∧" `prefixOf` x = And : tokenize  (drop 1 x)
  | "e" `prefixOf` x || "and" `prefixOf` x = And : tokenize  (drop 3 x)
  | "\\land" `prefixOf` x = And : tokenize  (drop 5 x)
  | "~" `prefixOf` x || "¬" `prefixOf` x = Not : tokenize  (drop 1 x)
  | "not" `prefixOf` x = Not : tokenize  (drop 3 x)
  | "\\neg" `prefixOf` x = Not : tokenize  (drop 4 x)
  | "¬" `prefixOf` x = Not : tokenize  (drop 1 x)
  | "->" `prefixOf` x || "=>" `prefixOf` x = Implication : tokenize  (drop 2 x)
  | "→" `prefixOf` x = Implication : tokenize  (drop 1 x)
  | "\\to" `prefixOf` x = Implication : tokenize  (drop 3 x)
  | "<->" `prefixOf` x || "<=>" `prefixOf` x = Biconditional : tokenize  (drop 3 x)
  | "↔" `prefixOf` x = Biconditional : tokenize  (drop 1 x)
  | "\\iff" `prefixOf` x = Biconditional : tokenize  (drop 4 x)
  | "true" `prefixOf` x = Booleano True : tokenize  (drop 4 x)
  | "false" `prefixOf` x = Booleano False : tokenize  (drop 5 x)
  | head x `elem` ['A' .. 'Z'] = Var (head x) : tokenize  (drop 1 x)
  | head x == ' ' || head x == '\t' = tokenize  (drop 1 x)
  | otherwise = error $ "Caractere inválido: " ++ [head x]

prefixOf :: String -> String -> Bool
prefixOf [] _ = True
prefixOf _ [] = False
prefixOf (x:xs) (y:ys) = x == y && prefixOf xs ys

-- Precedência dos operadores
precedencia :: Token -> Int
precedencia Not = 5
precedencia And = 4
precedencia Or = 3
precedencia Implication = 2
precedencia Biconditional = 1
precedencia LeftParen = 0
precedencia RightParen = 0

-- Função para converter expressão infixa para notação pós-fixa (RPN)
ordenar :: [Token] -> [Token] -> [Token] -> [Token]
ordenar [] [] o = o
ordenar [] (LeftParen : _) _ = error "Parêntese aberto sem fechamento"
ordenar [] (s : ss) o = ordenar [] ss (o ++ [s])
ordenar (Var r : xs) s o = ordenar xs s (o ++ [Var r])
ordenar (Booleano b : xs) s o = ordenar xs s (o ++ [Booleano b])
ordenar (LeftParen : xs) s o = ordenar xs (LeftParen : s) o
ordenar (RightParen : xs) (LeftParen : ss) o = ordenar xs ss o
ordenar (RightParen : xs) (s : ss) o = ordenar (RightParen : xs) ss (o ++ [s])
ordenar (x : xs) [] o = ordenar xs [x] o
ordenar (x : xs) (s : ss) o
  | precedencia x > precedencia s = ordenar xs (x : s : ss) o
  | otherwise = ordenar (x : xs) ss (o ++ [s])

-- Classificação de uma expressão como Tautologia, Contradição ou Contingente
classificar :: String -> String
classificar expr =
  let resultados = avaliarExpressao expr
  in if all id resultados then "Tautologia"
     else if not (any id resultados) then "Contradição"
     else "Contingente"

-- Avaliação da expressão para todas as combinações de valores booleanos das variáveis
avaliarExpressao :: String -> [Bool]
avaliarExpressao expr =
  let tokens = tokenize expr
      vars = variaveis tokens
      combinacoes = sequence (replicate (length vars) [True, False])
      rpn = ordenar tokens [] []
  in [evalExpr (zip vars c) rpn | c <- combinacoes]

variaveis :: [Token] -> [Char]
variaveis = foldl (\acc t -> case t of
  Var v -> if v `notElem` acc then v : acc else acc
  _ -> acc) []

-- Função para avaliar expressão RPN
evalExpr :: [(Char, Bool)] -> [Token] -> Bool
evalExpr vars = eval []
  where
    eval [result] [] = result
    eval stack (Var v : xs) = eval (lookupVar v : stack) xs
      where
        lookupVar var = case lookup var vars of
          Just value -> value
          Nothing -> error $ "Variável não encontrada: " ++ [var]
    eval stack (Booleano b : xs) = eval (b : stack) xs
    eval stack (Not : xs) = case stack of
      (s:rest) -> eval (not s : rest) xs
      _ -> error "Pilha insuficiente para operador 'Not'"
    eval stack (And : xs) = case stack of
      (s1:s2:rest) -> eval ((s2 && s1) : rest) xs
      _ -> error "Pilha insuficiente para operador 'And'"
    eval stack (Or : xs) = case stack of
      (s1:s2:rest) -> eval ((s2 || s1) : rest) xs
      _ -> error "Pilha insuficiente para operador 'Or'"
    eval stack (Implication : xs) = case stack of
      (s1:s2:rest) -> eval ((not s2 || s1) : rest) xs
      _ -> error "Pilha insuficiente para operador 'Implication'"
    eval stack (Biconditional : xs) = case stack of
      (s1:s2:rest) -> eval (((s2 && s1) || (not s2 && not s1)) : rest) xs
      _ -> error "Pilha insuficiente para operador 'Biconditional'"
    eval _ _ = error "Expressão inválida"
-- Tipo de dado para representar expressões proposicionais
data Proposicao
  = PVar Char
  | PBool Bool
  | PNao Proposicao
  | PConj Proposicao Proposicao
  | PDisj Proposicao Proposicao
  | PImpli Proposicao Proposicao
  | PBiCon Proposicao Proposicao
  deriving (Eq, Show)

-- Eliminar implicações e bicondicionais
transImplic :: Proposicao -> Proposicao
transImplic (PVar x) = PVar x
transImplic (PBool b) = PBool b
transImplic (PNao x) = PNao (transImplic x)
transImplic (PConj x y) = PConj (transImplic x) (transImplic y)
transImplic (PDisj x y) = PDisj (transImplic x) (transImplic y)
transImplic (PImpli x y) = PDisj (PNao (transImplic x)) (transImplic y)
transImplic (PBiCon x y) = PConj (transImplic (PImpli x y)) (transImplic (PImpli y x))

-- Mover negações para dentro e simplificar dupla negação
transNeg :: Proposicao -> Proposicao
transNeg (PVar x) = PVar x
transNeg (PBool b) = PBool b
transNeg (PNao (PNao x)) = transNeg x  -- Elimina dupla negação
transNeg (PNao (PConj x y)) = PDisj (transNeg (PNao x)) (transNeg (PNao y))  -- De Morgan
transNeg (PNao (PDisj x y)) = PConj (transNeg (PNao x)) (transNeg (PNao y))  -- De Morgan
transNeg (PNao x) = PNao (transNeg x)
transNeg (PConj x y) = PConj (transNeg x) (transNeg y)
transNeg (PDisj x y) = PDisj (transNeg x) (transNeg y)
-- Distribuir disjunções sobre conjunções para obter a FNC
distributivaProp :: Proposicao -> Proposicao
distributivaProp p =
  let p' = distribDisj p
  in if p == p' then p else distributivaProp p'

-- Distribuição parcial das disjunções sobre conjunções
distribDisj :: Proposicao -> Proposicao
distribDisj (PConj x y) = PConj (distribDisj x) (distribDisj y)
distribDisj (PDisj (PConj x y) z) = PConj (distribDisj (PDisj x z)) (distribDisj (PDisj y z))
distribDisj (PDisj z (PConj x y)) = PConj (distribDisj (PDisj z x)) (distribDisj (PDisj z y))
distribDisj (PDisj x y) = PDisj (distribDisj x) (distribDisj y)
distribDisj (PNao x) = PNao (distribDisj x)
distribDisj (PVar x) = PVar x
distribDisj (PBool x) = PBool x

-- Função principal para converter uma expressão para FNC
converterParaFNC :: Proposicao -> Proposicao
converterParaFNC = distributivaProp . transNeg . transImplic

parseRPN :: [Token] -> Proposicao
parseRPN = parse []
  where
    parse [result] [] = result
    parse stack (Var v : xs) = parse (PVar v : stack) xs
    parse stack (Booleano b : xs) = parse (PBool b : stack) xs
    parse (x : xs) (Not : rest) = parse (PNao x : xs) rest
    parse (y : x : xs) (And : rest) = parse (PConj x y : xs) rest
    parse (y : x : xs) (Or : rest) = parse (PDisj x y : xs) rest
    parse (y : x : xs) (Implication : rest) = parse (PImpli x y : xs) rest
    parse (y : x : xs) (Biconditional : rest) = parse (PBiCon x y : xs) rest
    parse _ _ = error "Expressão inválida para conversão em Proposicao"
    
-- Função para verificar se uma disjunção é uma cláusula de Horn
posiClausulaHorn :: Proposicao -> Bool
posiClausulaHorn (PDisj x y) = numPosi (PDisj x y) <= 1
posiClausulaHorn x = True  -- Um único literal é sempre uma cláusula de Horn

-- Contagem de literais positivos em uma expressão
numPosi:: Proposicao -> Int
numPosi (PVar _) = 1
numPosi (PNao _) = 0
numPosi (PDisj x y) = numPosi x + numPosi y
numPosi _ = 0

-- Separar as cláusulas da FNC
extrairClausulas :: Proposicao -> [Proposicao]
extrairClausulas (PConj x y) = extrairClausulas x ++ extrairClausulas y
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
toLatex (PVar x) = [x]
toLatex (PBool True) = "true"
toLatex (PBool False) = "false"
toLatex (PNao x) = "\\neg " ++ toLatex x
toLatex (PConj x y) = "(" ++ toLatex x ++ " \\land " ++ toLatex y ++ ")"
toLatex (PDisj x y) = "(" ++ toLatex x ++ " \\lor " ++ toLatex y ++ ")"
toLatex (PImpli x y) = "(" ++ toLatex x ++ " \\to " ++ toLatex y ++ ")"
toLatex (PBiCon x y) = "(" ++ toLatex x ++ " \\leftrightarrow " ++ toLatex y ++ ")"

-- Função para exibir a expressão em LaTeX e no terminal
printLaTeX :: String -> Proposicao -> IO ()
printLaTeX msg expr = do
    putStrLn $ msg ++ " (Terminal): " ++ show expr
    putStrLn $ msg ++ " (LaTeX): $$" ++ toLatex expr ++ "$$"

main :: IO ()
main = do
    let str = "P v (Q ^~Q) <-> P"
    let lexado = tokenize  str
    putStrLn $ "Tokens: " ++ show lexado
    printSeparator '=' 100
    let rpn = ordenar lexado [] []
    putStrLn $ "Notacaoo Pos-Fixa (RPN): " ++ show rpn
    putStrLn $ "Classificação da expressão: " ++ classificar str
    printSeparator '=' 100
    let prop = parseRPN rpn
    printLaTeX "Expressão Proposicional" prop
    let fnc = converterParaFNC prop
    printLaTeX "Expressão em FNC" fnc
    printSeparator '=' 100
    exibirClausulasHorn fnc
