type dense_t = float
type sparse_t = float

let cholesky_DC _matrixElem n mat = mat

let dense_elementwise_op _matrixElem (_nc: int) (_nl: int) (op: float -> float -> float) mat1 mat2 =
  Obj.magic (op (Obj.magic mat1) (Obj.magic mat2))

let dense_fill _matrixElem (nc: int) (nl: int) (fn: int -> int -> float) = Obj.magic (fn 0 0) (*  *)

let dense_get _matrixElem (_nc: int) (_nl: int) mat l c = (Obj.magic mat) (*  *)

let dense_mul _matrixElem (_nc: int) (_nc': int) (_nl: int) mat1 mat2  = Obj.magic ((Obj.magic mat1) *. (Obj.magic mat2)) (*  *)

let dense_sparse_mul _matrixElem n mat1 mat2 = Obj.magic ((Obj.magic mat1) *. (Obj.magic mat2)) (*  *)

let dense_sparse_mul_to_sparse _matrixElem n mat1 mat2 = Obj.magic ((Obj.magic mat1) *. (Obj.magic mat2)) (*  *)

let float_div x y = x /. y

let float_eq_dec x y = x = y

let float_inv x = 1. /. x

let float_minus x y = x -. y

let float_one = 1.0

let float_opp x = -. x

let float_plus x y = x +. y

let float_times x y = x *. y

let float_zero = 0.

let solveR_lower _matrixElem n mat1 mat2 = Obj.magic ((1. /. (Obj.magic mat1)) *. (Obj.magic mat2)) (*  *)

let solveR_upper _matrixElem n mat1 mat2 = Obj.magic ((1. /. (Obj.magic mat1)) *. (Obj.magic mat2)) (*  *)

let sparse_dense_mul _matrixElem n mat1 mat2 = Obj.magic ((Obj.magic mat1) *. (Obj.magic mat2)) (*  *)

let sparse_fill _matrixElem (nc: int) (nl: int) (fn: int -> int -> float) = Obj.magic (fn 0 0) (*  *)
