{-# LANGUAGE Strict #-}

import Data.List
import Control.Monad (when)

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
zCombinator = Abs "f" $ App inner inner
    where inner = Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))

-- Допишите функцию cbv, реализующую интерпретатор с окружениями
-- и вызовом по значению, согласно правилам в разделе 3.2
-- книги Довека, Леви.

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
cbn e (Let x t u) = cbn (extendEnv e x (Thunk t e)) u

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
cbv e (Let x t u) = cbv (extendEnv e x (cbv e t)) u

emptyEnv :: Env
emptyEnv = []

runCbv :: Term -> Value
runCbv = cbv emptyEnv


runCbn :: Term -> Value
runCbn = cbn emptyEnv

-- Проверьте работу cbv на термах t1, ..., t5.
-- Напишите функцию, вычисляющую факториал и проверьте ее работу
-- с помощью cbv.

fac :: Term
fac = Fix "f" $ Abs "n" $ Ifz (Var "n") (Const 1) (Times (Var "n") $ App (Var "f") (Minus (Var "n") (Const 1)))

facFix :: Term
facFix =  Abs "fact" (Abs "x" (Ifz (Var "x") (Const 1) (Times (Var "x") (App (Var "fact") (Minus (Var "x") (Const 1))))))

yFac :: Term
yFac = App yCombinator facFix

zFac :: Term
zFac = App zCombinator facFix
