import .ctypes

namespace clight
open ast ctypes integers

inductive expr : Type
  | Econst_int: int -> type -> expr       /- integer literal -/
  | Econst_float: float -> type -> expr   /- double float literal -/
  | Econst_single: float32 -> type -> expr /- single float literal -/
  | Econst_long: int64 -> type -> expr    /- long integer literal -/
  | Evar: ident -> type -> expr           /- variable -/
  | Etempvar: ident -> type -> expr       /- temporary variable -/
  | Ederef: expr -> type -> expr          /- pointer dereference (unary [*]) -/
  | Eaddrof: expr -> type -> expr         /- address-of operator ([&]) -/
  | Eunop: unary_operation -> expr -> type -> expr  /- unary operation -/
  | Ebinop: binary_operation -> expr -> expr -> type -> expr /- binary operation -/
  | Ecast: expr -> type -> expr   /- type cast ([(ty) e]) -/
  | Efield: expr -> ident -> type -> expr /- access to a member of a struct or union -/
  | Esizeof: type -> type -> expr         /- size of a type -/
  | Ealignof: type -> type -> expr        /- alignment of a type -/

end clight