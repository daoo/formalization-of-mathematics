module Debug where

import ToomCook

printSteps :: ToomCook -> Integer -> Integer -> IO ()
printSteps t n m = do
  putStrLn $ "b = " ++ show b
  putStrLn "split:"
  putStrLn $ "  n' = " ++ show n'
  putStrLn $ "  m' = " ++ show m'
  putStrLn "evaluate:"
  putStrLn $ "  n'' = " ++ show n''
  putStrLn $ "  m'' = " ++ show m''
  putStrLn "recursive:"
  putStrLn $ "  r = " ++ show r
  putStrLn "interpolate:"
  putStrLn $ "  r' = " ++ show r'
  putStrLn "recompose:"
  putStrLn $ "  r'' = " ++ show r''
  where
    b = 10^(baseExponent (toomK t) n m)
    n' = split (toomK t) b n
    m' = split (toomK t) b m

    n'' = evaluate (toomMat t) n'
    m'' = evaluate (toomMat t) m'

    r   = zipWith (toomCookRec t) n'' m''
    r'  = interpolate (toomInvMat t) r
    r'' = recompose b r'
