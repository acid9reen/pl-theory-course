{-# LANGUAGE Strict #-}

import Data.List
import Control.Monad (when)
import Text.XHtml (body)

data Term
    = Const Int
    | Var String
    | Abs String Term
    | App Term Term
    | Plus Term Term
    | Minus Term Term
    | Times Term Term
    | Ifz Term Term Term
    | Fix String Term
    | Let String Term Term
    | FixFun String String Term
    deriving Show

-- let x = s in t можно было не добавлять в ядро языка
-- а выразить через абстракцию и аппликацию.
-- let является ключевым словом, поэтому нужно другое имя.

llet :: String -> Term -> Term -> Term
llet x s t = App (Abs x t) s

-- Будем рассматривать замыкание (λx. M, rho) как тройку (x, M, rho).
-- Конструктор Thunk используется для помещения в окружение пары вида
-- (Fix x t, e). В разделе 3.2 книге ДЛ обычные значения или пары
-- такого вида называются оснащёнными значениями (extended values).

data Value
    = ValInt Int
    | Closure String Term Env
    | Thunk Term Env
    deriving Show

type Env = [(String, Value)]

-- Список [(x1, v1), ..., (xn, vn)] соответствует окружению
-- [(xn, vn), ..., (x1, v1)]. Напоминание: новые связывания
-- добавляются в окружение справа (слайд 17 лекции 5).
extendEnv :: Env -> String -> Value -> Env
extendEnv e x v = (x, v) : e

-- Call by name
cbn :: Env -> Term -> Value
cbn e (Const n) = ValInt n
cbn e (Var x) = case lookup x e of
    Just (Thunk (Fix y t) e') -> cbn (extendEnv e' y (Thunk (Fix y t) e')) t
    Just (Thunk t e') -> cbn e' t
    Just v -> v -- обычное (не оснащённое) значение
    Nothing -> error ("Variable " ++ x ++ " is not bound.")
cbn e (Abs x t) = Closure x t e
cbn e (App t u) = case cbn e t of
    Closure x t' e' -> cbn (extendEnv e' x (Thunk u e)) t'
    _ -> error "Applying a non-function value."
cbn e (Plus t u) = case (cbn e t, cbn e u) of
    (ValInt n, ValInt m) -> ValInt (n + m)
    _ -> error "Invalid addition."
cbn e (Minus t u) = case (cbn e t, cbn e u) of
    (ValInt n, ValInt m) -> ValInt (n - m)
    _ -> error "Invalid subtraction."
cbn e (Times t u) = case (cbn e t, cbn e u) of
    (ValInt n, ValInt m) -> ValInt (n * m)
    _ -> error "Invalid multiplication."
cbn e (Ifz c t u) = case cbn e c of
    ValInt 0 -> cbn e t
    ValInt _ -> cbn e u
    _ -> error "Invalid condition."
cbn e (Fix f t) = cbn (extendEnv e f (Thunk (Fix f t) e)) t
cbn e (FixFun f x t) = cbn e (Fix f (Abs x t))
cbn e (Let x t u) = cbn (extendEnv e x (Thunk t e)) u

runCbn :: Term -> Value
runCbn = cbn []

-- Call by value
cbv :: Env -> Term -> Value
cbv e (Const n) = ValInt n
cbv e (Var x) = case lookup x e of
    Just (Thunk (Fix y t) e') -> cbv (extendEnv e' y (Thunk (Fix y t) e')) t
    Just v -> v -- обычное (не оснащённое) значение
    Nothing -> error ("Variable " ++ x ++ " is not bound.")
cbv e (Abs x t) = Closure x t e
cbv e (App t u) = case cbv e t of
    Closure x t' e' -> cbv (extendEnv e' x (cbv e u)) t'
    _ -> error "Applying a non-function value."
cbv e (Plus t u) = case (cbv e t, cbv e u) of
    (ValInt n, ValInt m) -> ValInt (n + m)
    _ -> error "Invalid addition."
cbv e (Minus t u) = case (cbv e t, cbv e u) of
    (ValInt n, ValInt m) -> ValInt (n - m)
    _ -> error "Invalid subtraction."
cbv e (Times t u) = case (cbv e t, cbv e u) of
    (ValInt n, ValInt m) -> ValInt (n * m)
    _ -> error "Invalid multiplication."
cbv e (Ifz c t u) = case cbv e c of
    ValInt 0 -> cbv e t
    ValInt _ -> cbv e u
    _ -> error "Invalid condition."
cbv e (Fix f t) = cbv (extendEnv e f (Thunk (Fix f t) e)) t
cbv e (FixFun f x t) = cbv e (Fix f (Abs x t))
cbv e (Let x t u) = cbv (extendEnv e x (cbv e t)) u

runCbv :: Term -> Value
runCbv = cbv []

data ValueRC
    = ValIntRC Int
    | ClosureRC String String Term EnvRC
    deriving Show

type EnvRC = [(String, ValueRC)]

extendEnvRC :: EnvRC -> String -> ValueRC -> EnvRC
extendEnvRC e x ~v = (x, v) : e

-- Call by value recursive closures
cbvRC :: EnvRC -> Term -> ValueRC
cbvRC envRC (Const n) = ValIntRC n
cbvRC envRC (Var x) = case lookup x envRC of
    Just valRC -> valRC
    Nothing -> error ("Variable " ++ x ++ " is not bound.")
cbvRC envRC (Abs x t) = ClosureRC "rnd" x t envRC
cbvRC envRC (App t u) = case (cbvRC envRC t, cbvRC envRC u) of
    (ClosureRC f x t' envRC', u') ->
        cbvRC (extendEnvRC (extendEnvRC envRC' x u') f (ClosureRC f x t' envRC')) t'
    _ -> error "Applying a non-function value."
cbvRC envRC (Plus t u) = case (cbvRC envRC t, cbvRC envRC u) of
    (ValIntRC n, ValIntRC m) -> ValIntRC (n + m)
    _ -> error "Invalid addition."
cbvRC envRC (Minus t u) = case (cbvRC envRC t, cbvRC envRC u) of
    (ValIntRC n, ValIntRC m) -> ValIntRC (n - m)
    _ -> error "Invalid subtraction."
cbvRC envRC (Times t u) = case (cbvRC envRC t, cbvRC envRC u) of
    (ValIntRC n, ValIntRC m) -> ValIntRC (n * m)
    _ -> error "Invalid multiplication."
cbvRC envRC (Ifz c t u) = case cbvRC envRC c of
    ValIntRC 0 -> cbvRC envRC t
    ValIntRC _ -> cbvRC envRC u
    _ -> error "Invalid condition."
cbvRC envRC (Fix f t) = error "No fix in cbvRC!"
cbvRC envRC (FixFun f x t) = ClosureRC f x t envRC
cbvRC envRC (Let x t u) = cbvRC (extendEnvRC envRC x (cbvRC envRC t)) u

runCbvRC :: Term -> ValueRC
runCbvRC = cbvRC []

-- Термы для тестов

-- λx. x
t1 :: Term
t1 = Abs "x" (Var "x")

-- λx. 0
t2 :: Term
t2 = Abs "x" (Const 0)

-- Терм из лекции 5, слайд 23.
t3 :: Term
t3 = Let "x" (Const 1)
       (Let "f" (Abs "y" (Plus (Var "x") (Var "y")))
         (Let "x" (Const 2)
           (App (Var "f") (Const 3))))

-- Представление булевых значений.

tru :: Term
tru = Abs "x" (Abs "y" (Var "x"))

fls :: Term
fls = Abs "x" (Abs "y" (Var "y"))

cond :: Term
cond  = Abs "b" (Abs "x" (Abs "y" (App (App (Var "b") (Var "x")) (Var "y"))))

t4 :: Term
t4 = App (App (App cond tru) (Const 1)) (Const 0)

t5 :: Term
t5 = App (App (App cond fls) (Const 1)) (Const 0)

-- v1 = λx. x

v1 :: Value
v1 = Closure "x" (Var "x") []

-- v2 = (λy. f y, [f = (λx. x, [])])

v2 :: Value
v2 = Closure "y" (App (Var "f") (Var "y")) [("f", v1)]

-- fv t возвращает список свободных переменных в терме t.
-- Каждая переменная входит в список не более одного раза.

fv :: Term -> [String]
fv (Const _) = []
fv (Var x) = [x]
fv (Abs x u) = delete x (fv u)
fv (App t u) = nub $ fv t ++ fv u
fv (Plus t u) = nub $ fv t ++ fv u
fv (Minus t u) = nub $ fv t ++ fv u
fv (Times t u) = nub $ fv t ++ fv u
fv (Ifz c t u) = nub $ fv c ++ fv t ++ fv u
fv (Fix f u) = delete f (fv u)
fv (Let x t u) = nub $ fv t ++ delete x (fv u)

-- Y = λf. (λx.f (xx)) (λx.f (xx))
yCombinator :: Term
yCombinator = Abs "f" $ App inner inner
    where inner = Abs "x" $ App (Var "f") (App (Var "x") (Var "x"))


-- Z = λf. (λx.f (λy. xxy)) (λx.f (λy. xxy))
zCombinator :: Term
zCombinator = Abs "f" $ App inner inner
    where inner = Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))


-- Пример: app t [s1, s2, s3] = App (App (App t s1) s2) s3
app :: Term -> [Term] -> Term
app = foldl App

appr :: Term -> [Term] -> Term
appr = foldr App

-- Church numbers
-- Пример: intToChurch 3 = \s\z. s (s (s z))
intToChurch :: Int -> Term
intToChurch n =
    Abs "f" $ Abs "x" (appr (Var "x") (replicate n (Var "f")))

-- plus = λ m. λ n. λ s. λ z. m s (n s z)
plus :: Term
plus = Abs "m" $ Abs "n" $ Abs "s" $ Abs "z" $
    App (App (Var "m") (Var "s")) (App (App (Var "n") (Var "s")) (Var "z"))

-- times = λ m. λ n. m (plus n) 0
times :: Term
times = Abs "m" $ Abs "n" $ app (Var "m") [App plus (Var "n"), intToChurch 0]

checkOp :: (Term -> Value) -> Term -> Int -> Int -> Int
checkOp r t m n = churchToInt $ app t [intToChurch m, intToChurch n]
    where
        { churchToInt t
            = let ValInt n = r (app t [Abs "x" (Plus (Var "x") (Const 1)), Const 0]) in n }

seqBody :: Term
seqBody
    = Ifz (Var "count")
    (Var "start")
    $ app (Var "f")
        [ Plus (Times (Var "start") (Const 2)) (Const 5)
        , Minus (Var "count") (Const 1) ]

seqFixFun :: Term
seqFixFun = FixFun "f" "start" $ Abs "count" seqBody

seqTmpl :: Term
seqTmpl = Abs "start" $ Abs "count" seqBody

seqFix :: Term
seqFix = Fix "seq" seqTmpl

seqY :: Term
seqY = App yCombinator $ Abs "seq" seqTmpl

seqZ :: Term
seqZ = App zCombinator $ Abs "seq" seqTmpl

fact :: Term
fact
    = FixFun "f" "n"
    $ Ifz (Var "n")
        (Const 1)
        $ Times (Var "n") $ App (Var "f") $ Minus (Var "n") (Const 1)


-- <--------DB Indexes---------->


data TermDB
    = ConstDB Int
    | VarDB Int
    | AbsDB TermDB
    | AppDB TermDB TermDB
    | PlusDB TermDB TermDB
    | MinusDB TermDB TermDB
    | TimesDB TermDB TermDB
    | IfzDB TermDB TermDB TermDB
    | FixDB TermDB
    | LetDB TermDB TermDB
    | FixFunDB TermDB
    deriving Show

data ValueDB
    = ValIntDB Int
    | ClosureDB TermDB EnvDB
    | ThunkDB TermDB EnvDB
    deriving Show

type EnvDB = [ValueDB]


toDB :: Term -> TermDB
toDB = loop [] where
    loop :: [String] -> Term -> TermDB
    loop e (Abs x t) = AbsDB $ loop (x:e) t
    loop e (Fix x t) = FixDB $ loop (x:e) t
    loop e (FixFun f x t) = FixFunDB $ loop (f:x:e) t
    loop e (Let x t u) = LetDB (loop e t) (loop (x:e) u)
    loop e (Var x) = VarDB $ case elemIndex x e of
        Just n -> n
        Nothing -> error ("There is no variable" ++ x ++ "in env")
    loop e (Const c) = ConstDB c
    loop e (App t u) = AppDB (loop e t) (loop e u)
    loop e (Plus t u) = PlusDB (loop e t) (loop e u)
    loop e (Minus t u) = MinusDB (loop e t) (loop e u)
    loop e (Times t u) = TimesDB (loop e t) (loop e u)
    loop e (Ifz c t u) = IfzDB (loop e c) (loop e t) (loop e u)
