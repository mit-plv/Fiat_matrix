module KalmanAxioms
where

import Numeric.LinearAlgebra
import Unsafe.Coerce

type Float_t = Double
type SDM = Matrix Float_t
type SSM = Matrix Float_t

float_zero :: Float_t
float_zero = 0

float_one :: Float_t
float_one = 1

float_opp :: Float_t -> Float_t
float_opp = negate

float_plus :: Float_t -> Float_t -> Float_t
float_plus = (+)

float_minus :: Float_t -> Float_t -> Float_t
float_minus = (-)

float_times :: Float_t -> Float_t -> Float_t
float_times = (*)

float_div :: Float_t -> Float_t -> Float_t
float_div = (/)

float_inv :: Float_t -> Float_t
float_inv = (1 /)

float_eq_dec :: Float_t -> Float_t -> Bool
float_eq_dec = (==)

float_lt :: a -> a' -> Bool
float_lt x y = (unsafeCoerce x :: Float_t) < (unsafeCoerce y :: Float_t)

cholesky_DC :: a -> Int -> sdm -> sdm'
cholesky_DC _ _ a = unsafeCoerce (chol (trustSym (unsafeCoerce a :: SDM)))

dense_sparse_mul_to_sparse :: a -> Int -> sdm -> ssm -> ssm'
dense_sparse_mul_to_sparse _ _ a b = unsafeCoerce ((unsafeCoerce a :: SDM) <> (unsafeCoerce b :: SSM))

sparse_dense_mul :: a -> Int -> ssm -> sdm -> sdm'
sparse_dense_mul _ _ a b = unsafeCoerce ((unsafeCoerce a :: SSM) <> (unsafeCoerce b :: SDM))

dense_sparse_mul :: a -> Int -> sdm -> ssm -> sdm'
dense_sparse_mul _ _ a b = unsafeCoerce ((unsafeCoerce a :: SDM) <> (unsafeCoerce b :: SSM))

solveR_upper :: a -> Int -> sdm -> sdm -> sdm'
solveR_upper _ _ a b = unsafeCoerce ((unsafeCoerce a :: SDM) <\> (unsafeCoerce b :: SDM))

solveR_lower :: a -> Int -> sdm -> sdm -> sdm'
solveR_lower _ _ a b = unsafeCoerce ((unsafeCoerce a :: SDM) <\> (unsafeCoerce b :: SDM))

dense_get :: a -> Int -> Int -> sdm -> Int -> Int -> Float_t
dense_get _ _ _ m i j = (unsafeCoerce m :: SDM) `atIndex` (i, j)

dense_mul :: a -> Int -> Int -> Int -> sdm -> sdm' -> sdm''
dense_mul _ _ _ _ a b = unsafeCoerce ((unsafeCoerce a :: SDM) <> (unsafeCoerce b :: SDM))

dense_fill :: a -> Int -> Int -> (Int -> Int -> Float_t) -> sdm
dense_fill _ m n f = unsafeCoerce (fromLists [ [f i j | j <- [0..n - 1]] | i <- [0..m-1]] :: SDM)

dense_elementwise_op :: a -> Int -> Int -> (Float_t -> Float_t -> Float_t) -> SDM -> SDM -> SDM
dense_elementwise_op me m n f a b = dense_fill me m n (\i j -> f (a `atIndex` (i, j)) (b `atIndex` (i, j)))

sparse_get :: a -> Int -> Int -> SSM -> Int -> Int -> Float_t
sparse_get _ _ _ m i j = m `atIndex` (i, j)

sparse_mul :: a -> Int -> Int -> Int -> SSM -> SSM -> SSM
sparse_mul _ _ _ _ a b = a <> b

sparse_fill :: a ->  Int -> Int -> (Int -> Int -> Float_t) -> SSM
sparse_fill _ m n f = fromLists [ [f i j | j <- [0..n - 1]] | i <- [0..m-1]]

sparse_elementwise_op :: a -> Int -> Int -> (Float_t -> Float_t -> Float_t) -> SSM -> SSM -> SSM
sparse_elementwise_op me m n f a b = sparse_fill me m n (\i j -> f (a `atIndex` (i, j)) (b `atIndex` (i, j)))
