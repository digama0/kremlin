namespace errors

inductive errcode : Type
| MSG: string -> errcode
| CTX: pos_num -> errcode    /- a top-level identifier -/
| POS: pos_num -> errcode    /- a positive integer, e.g. a PC -/
export errcode (MSG CTX POS)

def errmsg: Type := list errcode

def msg (s: string) : errmsg := [MSG s]

inductive res (A : Type) : Type
| OK    {} : A -> res
| error {} : errmsg -> res
export res (OK error)

def res.bind {A B : Type} : res A → (A → res B) → res B
| (OK a) f := f a
| (error e) _ := error e

instance : monad res :=
{ pure := @OK, bind := @res.bind,
  id_map := sorry,
  pure_bind := sorry,
  bind_assoc := sorry }

end errors