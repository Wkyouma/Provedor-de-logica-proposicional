-- Tipos de dados para os tokens e expressões proposicionais
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

-- Função para tokenizar uma string em tokens
lexer :: String -> [Token]
lexer [] = []
lexer x
  | "(" `prefixOf` x = LeftParen : lexer (drop 1 x)
  | ")" `prefixOf` x = RightParen : lexer (drop 1 x)
  | "v" `prefixOf` x || "∨" `prefixOf` x = Or : lexer (drop 1 x)
  | "ou" `prefixOf` x || "or" `prefixOf` x = Or : lexer (drop 2 x)
  | "^" `prefixOf` x || "∧" `prefixOf` x = And : lexer (drop 1 x)
  | "e" `prefixOf` x || "and" `prefixOf` x = And : lexer (drop 3 x)
  | "~" `prefixOf` x || "¬" `prefixOf` x = Not : lexer (drop 1 x)
  | "not" `prefixOf` x = Not : lexer (drop 3 x)
  | "->" `prefixOf` x || "=>" `prefixOf` x = Implication : lexer (drop 2 x)
  | "<->" `prefixOf` x || "<=>" `prefixOf` x = Biconditional : lexer (drop 3 x)
  | "true" `prefixOf` x = Booleano True : lexer (drop 4 x)
  | "false" `prefixOf` x = Booleano False : lexer (drop 5 x)
  | head x `elem` ['A' .. 'Z'] = Var (head x) : lexer (drop 1 x)
  | head x == ' ' || head x == '\t' = lexer (drop 1 x)
  | otherwise = error $ "Caractere inválido: " ++ [head x]

prefixOf :: String -> String -> Bool
prefixOf [] _ = True
prefixOf _ [] = False
prefixOf (x:xs) (y:ys) = x == y && prefixOf xs ys

-- Precedência dos operadores
precedencia :: Token -> Int
precedencia Not = 6
precedencia And = 5
precedencia Or = 4
precedencia Implication = 3
precedencia Biconditional = 2
precedencia LeftParen = 1
precedencia RightParen = 1

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
  let tokens = lexer expr
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

data Prop
  = PVar Char
  | PBool Bool
  | PNao Prop
  | PConj Prop Prop
  | PDisj Prop Prop
  | PImpli Prop Prop
  | PBiCon Prop Prop
  deriving (Eq, Show)

-- Eliminar implicações e bicondicionais
elimImpli :: Prop -> Prop
elimImpli (PVar x) = PVar x
elimImpli (PBool b) = PBool b
elimImpli (PNao x) = PNao (elimImpli x)
elimImpli (PConj x y) = PConj (elimImpli x) (elimImpli y)
elimImpli (PDisj x y) = PDisj (elimImpli x) (elimImpli y)
elimImpli (PImpli x y) = PDisj (PNao (elimImpli x)) (elimImpli y)
elimImpli (PBiCon x y) = PConj (elimImpli (PImpli x y)) (elimImpli (PImpli y x))

-- Mover negações para dentro e simplificar dupla negação
elimNeg :: Prop -> Prop
elimNeg (PVar x) = PVar x
elimNeg (PBool b) = PBool b
elimNeg (PNao (PNao x)) = elimNeg x  -- Elimina dupla negação
elimNeg (PNao (PConj x y)) = PDisj (elimNeg (PNao x)) (elimNeg (PNao y))  -- De Morgan
elimNeg (PNao (PDisj x y)) = PConj (elimNeg (PNao x)) (elimNeg (PNao y))  -- De Morgan
elimNeg (PNao x) = PNao (elimNeg x)
elimNeg (PConj x y) = PConj (elimNeg x) (elimNeg y)
elimNeg (PDisj x y) = PDisj (elimNeg x) (elimNeg y)

-- Distribuir disjunções sobre conjunções para obter a FNC
distributivaProp :: Prop -> Prop
distributivaProp p =
  let p' = distribDisj p
  in if p == p' then p else distributivaProp p'

-- Distribuição parcial das disjunções sobre conjunções
distribDisj :: Prop -> Prop
distribDisj (PConj x y) = PConj (distribDisj x) (distribDisj y)
distribDisj (PDisj (PConj x y) z) = PConj (distribDisj (PDisj x z)) (distribDisj (PDisj y z))
distribDisj (PDisj z (PConj x y)) = PConj (distribDisj (PDisj z x)) (distribDisj (PDisj z y))
distribDisj (PDisj x y) = PDisj (distribDisj x) (distribDisj y)
distribDisj (PNao x) = PNao (distribDisj x)
distribDisj (PVar x) = PVar x
distribDisj (PBool x) = PBool x

-- Função principal para converter uma expressão para FNC
converterParaFNC :: Prop -> Prop
converterParaFNC = distributivaProp . elimNeg . elimImpli

parseRPN :: [Token] -> Prop
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
    parse _ _ = error "Expressão inválida para conversão em Prop"

-- Atualização do `main` para automatizar a conversão para `Prop` e FNC
main :: IO ()
main = do
    -- Expressão a ser analisada
    let str = "X <-> Y"
    
    -- Etapa 1: Tokenização da string
    let lexado = lexer str
    putStrLn $ "Tokens: " ++ show lexado
    
    -- Etapa 2: Conversão para notação pós-fixa (RPN) usando o Shunting Yard
    let rpn = ordenar lexado [] []
    putStrLn $ "Notação Pós-Fixa (RPN): " ++ show rpn
    
    -- Etapa 3: Classificação da expressão como Tautologia, Contradição ou Contingente
    let classificacao = classificar str
    putStrLn $ "Classificação da expressão: " ++ classificacao
    
    -- Etapa 4: Converter a notação RPN para uma expressão `Prop`
    let exprProp = parseRPN rpn
    putStrLn $ "Expressão Prop: " ++ show exprProp
    
    -- Etapa 5: Converter a expressão `Prop` para FNC
    let exprFNC = converterParaFNC exprProp
    putStrLn $ "Expressão em FNC: " ++ show exprFNC