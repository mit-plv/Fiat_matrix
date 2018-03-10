#use "topfind";;
Topfind.don't_load ["compiler-libs.toplevel"];; 
#require "owl";;
open Owl;;
#require "owl_top";;

let x = Mat.eye 5;;

let cholesky_DC _matrixElem n mat = mat

let dense_fill _matrixElem (nc: int) (nl: int) (fn: int -> int -> float) = Mat.init_2d nc nl fn;; (*  *)

let dense_get _matrixElem (_nc: int) (_nl: int) mat l c = Mat.get mat l c;; (*  *)

let dense_elementwise_op _matrixElem (_nc: int) (_nl: int) (op: float -> float -> float) mat1 mat2 =
  dense_fill _matrixElem _nc _nl (fun x y -> op (dense_get _matrixElem _nc _nl mat1 x y) (dense_get _matrixElem _nc _nl mat2 x y));;

let dense_mul _matrixElem (_nc: int) (_nc': int) (_nl: int) mat1 mat2  = Mat.(mat1 * mat2);; (*  *)

let dense_sparse_mul _matrixElem n mat1 mat2 = Mat.(mat1 * (Owl_sparse_matrix.D.to_dense mat2));; (*  *)

let dense_sparse_mul_to_sparse _matrixElem n mat1 mat2 = Owl_sparse_matrix.D.of_dense (dense_sparse_mul _matrixElem n mat1 mat2);; (*  *)

let float_div x y = x /. y

let float_eq_dec x y = x = y

let float_inv x = 1. /. x

let float_minus x y = x -. y

let float_one = 1.0

let float_opp x = -. x

let float_plus x y = x +. y

let float_times x y = x *. y

let float_zero = 0.

let solveR_lower _matrixElem n mat1 mat2 = Mat.(Mat.inv mat1 * mat2);; (*  *)

let solveR_upper _matrixElem n mat1 mat2 = Mat.(Mat.inv mat1 * mat2);; (*  *)

let sparse_dense_mul _matrixElem n mat1 mat2 = Mat.((Owl_sparse_matrix.D.to_dense mat2) * mat1);; (*  *)

let sparse_fill _matrixElem (nc: int) (nl: int) (fn: int -> int -> float) = Owl_sparse_matrix.D.of_dense (dense_fill _matrixElem nc nl fn);; (*  *)
