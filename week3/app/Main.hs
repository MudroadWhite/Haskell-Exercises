module Main (
    module Main
    )
where

-- import Lib
data ByteCode = ADD | SUB | MUL | DIV 
              | LOAD Int | READ String | WRITE String | RETURN
              -- New loop support
              | REPEAT Int | ENDREP

type Var = (String, Int)
-- vars, vals, and Bytecodes of where the loop starts
type Env = ([Var], [Int], [[ByteCode]])

emptyenv = ([], [], [])



runByteCode :: [ByteCode] -> Env -> Maybe Int
runByteCode [] _ = Nothing
runByteCode (c:cs) env@(vars, vals, loop) =
    case c of
        ADD     -> check (runByteCode cs) (op (+) env)
        SUB     -> check (runByteCode cs) (op (-) env)
        MUL     -> check (runByteCode cs) (op (*) env)
        DIV     -> check (runByteCode cs) (op div env)
        LOAD x  -> runByteCode cs (vars, pushval x vals, loop)
        READ x  -> case getvar x vars of
                    Just y       -> runByteCode cs (vars, pushval y vals, loop)
                    Nothing      -> Nothing
        WRITE x -> case popval vals of
                    Just (y, vs) -> runByteCode cs $ pushvar x y vars vals
                    Nothing      -> Nothing
        RETURN  -> case popval vals of
                    Just (x, _)  -> Just x
                    _            -> Nothing
        REPEAT x -> if x > 0 then runByteCode cs (pushloop (REPEAT (x-1) : cs) env)
                    else runByteCode cs env
        ENDREP   -> renewRun env
    where
        -- getvar finds a value associated with a variable name
        getvar :: String -> [Var] -> Maybe Int
        getvar x [] = Nothing 
        getvar x (v:vs) = if x == fst v then Just (snd v) else getvar x vs

        -- popvar pops a value from the constant stack
        popval :: [Int] -> Maybe (Int, [Int])
        popval [] = Nothing
        popval (x:xs) = Just (x, xs)

        -- pushval pushes a value into the stack
        pushval = (:)

        -- Since we've already done the check to ensure 
        -- there is value to use, push var only combines the
        -- existing information into an env
        pushvar x y vars vals = ((x, y):vars, vals, loop)

        -- op is a general function that takes an operator 
        -- to operate on two values
        op :: (Int -> Int -> Int) -> Env -> Maybe Env
        op f env@(vars, vals, loop) = case popval vals of
                Nothing -> Nothing
                Just (x1, vals1) -> case popval vals1 of
                    Nothing -> Nothing
                    Just (x2, vals2) -> 
                        Just (vars, f x1 x2:vals2, loop)

        -- Simple function to eliminate `case of` boilerplates
        check = maybe Nothing

        -- pushes loop into an environment
        pushloop cs env@(vs, vl, loops) = (vs, vl, cs : loops)

        -- pops the loops from an environment
        poploop env@(_, _, loops) = (head loops, tail loops)

        renewRun env@(vs, vl, _) =
            let (l, ls)      = poploop env in
                case head l of
                    REPEAT x ->
                        if x > 0 then
                            runByteCode (tail l) 
                                (vs, vl, (REPEAT (x-1) : tail l) : ls)
                        else
                            runByteCode cs (vs, vl, ls)
                    _ -> runByteCode cs (vs, vl, ls)

-- Test: normal loops usages
-- >>> cmd = [LOAD 1, REPEAT 1, LOAD 1, ADD, ENDREP, RETURN]
-- >>> runByteCode cmd emptyenv
-- Just 2

-- >>> cmd = [LOAD 1, REPEAT 2, LOAD 1, ADD, ENDREP, RETURN]
-- >>> runByteCode cmd emptyenv
-- Just 3

-- Test: 0 loop should be ignored
-- >>> cmd = [LOAD 1, REPEAT 0, LOAD 1, ADD, ENDREP, RETURN]
-- >>> runByteCode cmd emptyenv
-- Prelude.head: empty list


main :: IO () 
main = return ()
