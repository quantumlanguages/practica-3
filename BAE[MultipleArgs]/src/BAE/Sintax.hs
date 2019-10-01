{--
Practica 3
El lenguaje MiniHS (EAB extendido con cáculo lambda). Sintaxis
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

module BAE.Sintax where

    -- Importing some useful list functions
    import Data.List
    import Text.Read

    -- Extending the sintax

    -- | Renaming String to Identifier in order to use text as variables' name.
    type Identifier = String

    -- | Defining the expresions of the language. Same as before, but now with
    -- variables
    data Expr = V Identifier | I Int | B Bool -- ^ Basic expresions
                | Add Expr Expr | Mul Expr Expr -- ^ Binary arithmetic operations
                | Succ Expr | Pred Expr -- ^ Unary arithmetic operations
                | Not Expr | And Expr Expr | Or Expr Expr -- ^ Logical operations
                | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr -- ^ Comparaison operations
                | If Expr Expr Expr -- ^ If operation
                | Let Identifier Expr Expr -- ^ Variable declaration and bounding operation
                | Fn Identifier Expr -- ^ Lambda functions
                | App Expr Expr -- ^ Function application
                deriving (Eq)

    -- | Implementing the Show class to make expression visualization prettier.
    instance Show Expr where
      show e = case e of
            (V x) -> "V[" ++ x ++ "]"
            (I n) -> "N[" ++ (show n) ++ "]"
            (B b) -> "B[" ++ (show b) ++ "]"
            (Add e1 e2) -> "add("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Mul e1 e2) -> "mul("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Succ e1) -> "suc(" ++ (show e1) ++ ")"
            (Pred e1) -> "pred(" ++ (show e1) ++ ")"
            (Not e1) -> "not(" ++ (show e1) ++ ")"
            (And e1 e2) -> "and["++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Or e1 e2) -> "or("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Lt e1 e2) -> "lt("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Gt e1 e2) -> "gt("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Eq e1 e2) -> "eq("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (If ec e1 e2) -> "if("++ (show ec) ++ " , " ++ (show e1) ++ " , "
                           ++ (show e2) ++ ")"
            (Let x e1 e2) -> "let(" ++ (show e1) ++ " , " ++ (show x) ++ "." ++ (show e2) ++ ")"
            (Fn x e1) -> "fn(" ++ x ++ "." ++ (show e1) ++ ")"
            (App e1 e2) -> "app(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"

    -- Defining some semantics

    -- | Variable asignation will be emulated using textual sustitution
    type Substitution = (Identifier, Expr)

    -- | Obtaining the free variables from an expression
    frVars :: Expr -> [Identifier]
    frVars ex =
        case ex of
            (V x) -> [x]
            (I _) -> []
            (B _) -> []
            (Add e f) -> union (frVars e) (frVars f)
            (Mul e f) -> union (frVars e) (frVars f)
            (Succ e) -> frVars e
            (Pred e) -> frVars e
            (Not e) -> frVars e
            (And e f) -> union (frVars e) (frVars f)
            (Or e f) -> union (frVars e) (frVars f)
            (Lt e f) -> union (frVars e) (frVars f)
            (Gt e f) -> union (frVars e) (frVars f)
            (Eq e f) -> union (frVars e) (frVars f)
            (If e f g) -> union (union (frVars e) (frVars f)) (frVars g)
            (Let i e f) -> union (frVars e) ((frVars f) \\ [i])
            (Fn i e) -> (frVars e) \\ [i]
            (App e f) -> union (frVars e) (frVars f)

    -- | Increases the numerical suffix of an identifier. If no numerical value
    -- is present, then it adds '1' at the end of the identifier.
    incrVar :: Identifier -> Identifier
    incrVar x = incrVarAux [] x

    -- | Tail recursion implementation of incrVar.
    -- Uses 'Text.Read.readMaybe' to try to parse the suffix of the identifier.
    incrVarAux :: Identifier -> Identifier -> Identifier
    incrVarAux a [] = a ++ "1"
    incrVarAux a y@(x:xs) =
        case readMaybe y of
            Nothing -> incrVarAux (a ++ [x]) xs
            Just n -> a ++ (show ((n+1) :: Integer))

    -- | Obtaning a variable name not present in an expression as a free variable
    safeName :: Identifier -> Expr -> Identifier
    safeName x e = 
        let x' = (incrVar x) in
            if elem x' (frVars e)
                then safeName x' e
                else x'

    -- | Alpha reduction
    alphaExpr :: Expr -> Expr
    alphaExpr e = 
        case e of
            Let x e1 e2 ->
                let x' = safeName x e2; e2' = subst e2 (x, V x') in
                    Let x' e1 e2'
            Fn x e1 -> 
                let x' = safeName x e1; e1' = subst e1 (x, V x') in
                    Fn x' e1'
            _ -> e


    -- | Applying subtition if semantically possible
    subst :: Expr -> Substitution -> Expr
    subst ex s@(y, e') =
        case ex of
            (V x) ->
                if x == y then e' else ex
            (I _) -> ex
            (B _) -> ex
            (Add e f) -> Add (st e) (st f)
            (Mul e f) -> Mul (st e) (st f)
            (Succ e) -> Succ (st e)
            (Pred e) -> Pred (st e)
            (Not e) -> Not (st e)
            (And e f) -> And (st e) (st f)
            (Or e f) -> Or (st e) (st f)
            (Lt e f) -> Lt (st e) (st f)
            (Gt e f) -> Gt (st e) (st f)
            (Eq e f) -> Eq (st e) (st f)
            (If e f g) -> If (st e) (st f) (st g)
            (Let x e f) ->
                if x == y || elem x (frVars e')
                    then st (alphaExpr ex)
                    else Let x (st e) (st f)
            (Fn x e) ->
                if x == y || elem x (frVars e')
                    then st (alphaExpr ex)
                    else Fn x (st e)
            (App e f) -> Or (st e) (st f)
        where st = (flip subst) s
