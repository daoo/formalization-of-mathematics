module Settings where

import Data.Ratio
import ToomCook

-- NOTE: The rows in the evaluation matrices are inverted

toom1 :: ToomCook
toom1 = ToomCook 1 [[1]] [[1]]

karatsuba :: ToomCook
karatsuba = ToomCook 2
  [ reverse [ 1 , 0 ]
  , reverse [ 1 , 1 ]
  , reverse [ 0 , 1 ]
  ]
  [ [1  , 0 , 0  ]
  , [-1 , 1 , -1 ]
  , [0  , 0 , 1  ]
  ]

toom3 :: ToomCook
toom3 = ToomCook 3
  [ [ 0 , 0  , 1 ]
  , [ 1 , 1  , 1 ]
  , [ 1 , -1 , 1 ]
  , [ 4 , -2 , 1 ]
  , [ 1 , 0  , 0 ]
  ]
  [ [ 1    , 0   , 0   , 0    , 0  ]
  , [ 1%2  , 1%3 , -1  , 1%6  , -2 ]
  , [ -1   , 1%2 , 1%2 , 0    , -1 ]
  , [ -1%2 , 1%6 , 1%2 , -1%6 , 2  ]
  , [ 0    , 0   , 0   , 0    , 1  ]
  ]

toom4 :: ToomCook
toom4 = ToomCook 4
  [ reverse [ 1 , 0  , 0 , 0  ]
  , reverse [ 1 , 1  , 1 , 1  ]
  , reverse [ 1 , -1 , 1 , -1 ]
  , reverse [ 1 , -2 , 4 , -8 ]
  , reverse [ 1 , 2  , 4 , 8  ]
  , reverse [ 1 , 3  , 9 , 27 ]
  , reverse [ 0 , 0  , 0 , 1  ]
  ]
  [ [ 1     , 0     , 0     , 0      , 0     , 0     , 0   ]
  , [ -1%3  , 1     , -1%2  , 1%20   , -1%4  , 1%30  , -12 ]
  , [ -5%4  , 2%3   , 2%3   , -1%24  , -1%24 , 0     , 4   ]
  , [ 5%12  , -7%12 , -1%24 , -1%24  , 7%24  , -1%24 , 15  ]
  , [ 1%4   , -1%6  , -1%6  , 1%24   , 1%24  , 0     , -5  ]
  , [ -1%12 , 1%12  , 1%24  , -1%120 , -1%24 , 1%120 , -3  ]
  , [ 0     , 0     , 0     , 0      , 0     , 0     , 1   ]
  ]
