/- Separate compilation and syntactic linking -/

import .ast .maps .lib

/- This file follows "approach A" from the paper
       "Lightweight Verification of Separate Compilation"
    by Kang, Kim, Hur, Dreyer and Vafeiadis, POPL 2016. -/


namespace linking
open ast maps

/- * Syntactic linking -/

/- A syntactic element [A] supports syntactic linking if it is equipped with the following:
- a partial binary operator [link] that produces the result of linking two elements,
  or fails if they cannot be linked (e.g. two definitions that are incompatible);
- a preorder [linkorder] with the meaning that [linkorder a1 a2] holds
  if [a2] can be obtained by linking [a1] with some other syntactic element.
-/

class linker (A : Type) :=
(link : A → A → option A)
(linkorder : A → A → Prop)
(linkorder_refl : ∀ x, linkorder x x)
(linkorder_trans : ∀ {x y z}, linkorder x y → linkorder y z → linkorder x z)
(link_linkorder : ∀ {x y z}, link x y = some z → linkorder x z ∧ linkorder y z)
export linker (link linkorder)

/- Linking variable initializers.  We adopt the following conventions:
- an "extern" variable has an empty initialization list;
- a "common" variable has an initialization list of the form [Init_space sz];
- all other initialization lists correspond to fully defined variables, neither "common" nor "extern".
-/

inductive init_class : list init_data → Type
| extern : init_class []
| common (sz) : init_class [init_data.space sz]
| definitive (il) : init_class il

def classify_init : Π (i : list init_data), init_class i
| [] := init_class.extern
| [init_data.space sz] := init_class.common sz
| i := init_class.definitive i

def link_varinit (i1 i2 : list init_data) :=
match i1, i2, classify_init i1, classify_init i2 with
| ._, i2, init_class.extern, _ := some i2
| i1, ._, _, init_class.extern := some i1
| ._, i2, init_class.common sz1, _ := if sz1 = init_data_list_size i2 then some i2 else none
| i1, ._, _, init_class.common sz2 := if sz2 = init_data_list_size i1 then some i1 else none
| i1, i2, _, _ := none
end.

inductive linkorder_varinit : list init_data → list init_data → Prop
| linkorder_varinit_refl (il) : linkorder_varinit il il
| linkorder_varinit_extern (il) : linkorder_varinit [] il
| linkorder_varinit_common {sz il} :
    il ≠ [] → init_data_list_size il = sz →
    linkorder_varinit [init_data.space sz] il.

instance Linker_varinit : linker (list init_data) :=
{ link := link_varinit,
  linkorder := linkorder_varinit,
  linkorder_refl := sorry,
  linkorder_trans := sorry,
  link_linkorder := sorry }

/- Linking variable definitions. -/

def link_vardef {V} [linker V] (v1 v2 : globvar V) : option (globvar V) :=
  match link v1.gvar_info v2.gvar_info with
  | none := none
  | some info :=
      match link v1.gvar_init v2.gvar_init with
      | none := none
      | some init :=
          if v1.gvar_readonly = v2.gvar_readonly ∧
             v1.gvar_volatile = v2.gvar_volatile
          then some { gvar_info := info, gvar_init := init,
                      gvar_readonly := v1.gvar_readonly,
                      gvar_volatile := v1.gvar_volatile }
          else none
      end
  end.

inductive linkorder_vardef {V} [linker V] : globvar V → globvar V → Prop
| intro {info1 info2 i1 i2} {ro vo} :
    linkorder info1 info2 →
    linkorder i1 i2 →
    linkorder_vardef ⟨info1, i1, ro, vo⟩ ⟨info2, i2, ro, vo⟩

instance Linker_vardef {V} [linker V] : linker (globvar V) :=
{ link := link_vardef,
  linkorder := linkorder_vardef,
  linkorder_refl := sorry,
  linkorder_trans := sorry,
  link_linkorder := sorry }

/- Linking global definitions -/

def link_def {F V} [linker F] [linker V] : globdef F V → globdef F V → option (globdef F V)
| (Gfun f1) (Gfun f2) := Gfun <$> link f1 f2
| (Gvar v1) (Gvar v2) := Gvar <$> link v1 v2
| _ _ := none

inductive linkorder_def {F V} [linker F] [linker V] : globdef F V → globdef F V → Prop
| linkorder_def_fun (fd1 fd2) :
    linkorder fd1 fd2 →
    linkorder_def (Gfun fd1) (Gfun fd2)
| linkorder_def_var (v1 v2) :
    linkorder v1 v2 →
    linkorder_def (Gvar v1) (Gvar v2).

instance Linker_def {F V} [linker F] [linker V] : linker (globdef F V) :=
{ link := link_def,
  linkorder := linkorder_def,
  linkorder_refl := sorry,
  linkorder_trans := sorry,
  link_linkorder := sorry }

/- Linking two compilation units.  Compilation units are represented like
  whole programs using the type [program F V].  If a name has
  a global definition in one unit but not in the other, this definition
  is left unchanged in the result of the link.  If a name has
  global definitions in both units, and is public (not static) in both,
  the two definitions are linked as per [Linker_def] above.  

  If one or both definitions are static (not public), we should ideally
  rename it so that it can be kept unchanged in the result of the link.
  This would require a general notion of renaming of global identifiers
  in programs that we do not have yet.  Hence, as a first step, linking
  is undefined if static definitions with the same name appear in both
  compilation units. -/

section linker_prog
parameters {F V : Type} [linker F] [linker V]

section
parameters (p1 p2 : program F V)

def dm1 := prog_defmap p1
def dm2 := prog_defmap p2

def link_prog_check (x : ident) (gd1 : globdef F V) :=
match dm2^!x with
| none := tt
| some gd2 := (x ∈ p1.prog_public) && (x ∈ p2.prog_public) && (link gd1 gd2).is_some
end

def link_prog_merge : option (globdef F V) → option (globdef F V) → option (globdef F V)
| none o2 := o2
| o1 none := o1
| (some gd1) (some gd2) := link gd1 gd2

def link_prog : option (program F V) :=
if p1.prog_main = p2.prog_main ∧ PTree.for_all dm1 link_prog_check then
some { prog_main := p1.prog_main,
       prog_public := p1.prog_public ++ p2.prog_public,
       prog_defs := PTree.elements $ PTree.combine link_prog_merge dm1 dm2 }
else none

lemma link_prog_inv (p) (h : link_prog = some p) :
      p1.prog_main = p2.prog_main
   ∧ (∀ (id : ident) gd1 gd2,
         (dm1^!id) = some gd1 → (dm2^!id) = some gd2 →
         id ∈ p1.prog_public ∧ id ∈ p2.prog_public ∧ ∃ gd, link gd1 gd2 = some gd)
  ∧ p = { prog_main := p1.prog_main,
          prog_public := p1.prog_public ++ p2.prog_public,
          prog_defs := PTree.elements (PTree.combine link_prog_merge dm1 dm2) } := sorry

lemma link_prog_succeeds (hp : p1.prog_main = p2.prog_main)
  (h : ∀ (id : ident) gd1 gd2,
       (dm1^!id) = some gd1 → (dm2^!id) = some gd2 →
       id ∈ p1.prog_public ∧ id ∈ p2.prog_public ∧ (link gd1 gd2).is_some) :
  link_prog = some {
    prog_main := p1.prog_main,
    prog_public := p1.prog_public ++ p2.prog_public,
    prog_defs := PTree.elements (PTree.combine link_prog_merge dm1 dm2) } := sorry

lemma prog_defmap_elements (m: PTree.t (globdef F V)) (pub mn x) :
  (prog_defmap ⟨PTree.elements m, pub, mn⟩ ^! x) = (m^!x) := sorry
end

instance linker_prog : linker (program F V) :=
{ link := link_prog,
  linkorder := λp1 p2, p1.prog_main = p2.prog_main
  ∧ p1.prog_public ⊆ p2.prog_public
  ∧ ∀ (id : ident) gd1, (prog_defmap p1^!id) = some gd1 →
     ∃ gd2, (prog_defmap p2^!id) = some gd2 ∧
       linkorder gd1 gd2 ∧ (id ∉ p2.prog_public → gd2 = gd1),
  linkorder_refl := sorry,
  linkorder_trans := sorry,
  link_linkorder := sorry }

lemma prog_defmap_linkorder {p1 p2 : program F V} {id gd1} :
  linkorder p1 p2 →
  (prog_defmap p1^!id) = some gd1 →
  ∃ gd2, (prog_defmap p2^!id) = some gd2 ∧ linkorder gd1 gd2 := sorry

end linker_prog

/- * Matching between two programs -/

/- The following is a relational presentation of program transformations,
  e.g. [transf_partial_program] from module [AST].  -/

/- To capture the possibility of separate compilation, we parameterize
  the [match_fundef] relation between function definitions with
  a context, e.g. the compilation unit from which the function definition comes.
  This unit is characterized as any program that is in the [linkorder]
  relation with the final, whole program. -/

section match_program_generic

parameters {C F1 V1 F2 V2 : Type} -- [linker F1] [linker V1]
parameter match_fundef : C → F1 → F2 → Prop
parameter match_varinfo : V1 → V2 → Prop

inductive match_globvar : globvar V1 → globvar V2 → Prop
| mk (i1 i2 init ro vo) :
  match_varinfo i1 i2 →
  match_globvar ⟨i1, init, ro, vo⟩ ⟨i2, init, ro, vo⟩

variable [linker C]

inductive match_globdef (ctx : C) : globdef F1 V1 → globdef F2 V2 → Prop
| func (ctx' f1 f2) :
  linkorder ctx' ctx →
  match_fundef ctx' f1 f2 →
  match_globdef (Gfun f1) (Gfun f2)
| var {v1 v2} :
  match_globvar v1 v2 →
  match_globdef (Gvar v1) (Gvar v2).

def match_ident_globdef (ctx : C) : ident × globdef F1 V1 → ident × globdef F2 V2 → Prop
| (i1, g1) (i2, g2) := i1 = i2 ∧ match_globdef ctx g1 g2

def match_program_gen (ctx : C) (p1 : program F1 V1) (p2 : program F2 V2) : Prop :=
list.forall2 (match_ident_globdef ctx) p1.prog_defs p2.prog_defs
∧ p2.prog_main = p1.prog_main
∧ p2.prog_public = p1.prog_public

theorem match_program_defmap {ctx p1 p2} (hm : match_program_gen ctx p1 p2) (id) :
  option.rel (match_globdef ctx) (prog_defmap p1^!id) (prog_defmap p2^!id) := sorry

lemma match_program_gen_main {ctx p1 p2} (hm : match_program_gen ctx p1 p2) :
  p2.prog_main = p1.prog_main := sorry

lemma match_program_public {ctx p1 p2} (hm : match_program_gen ctx p1 p2) :
  p2.prog_public = p1.prog_public := sorry

end match_program_generic

/- In many cases, the context for [match_program_gen] is the source program or 
  source compilation unit itself.  We provide a specialized definition for this case. -/

def match_program {F1 V1 F2 V2} [linker F1] [linker V1]
  (match_fundef : program F1 V1 → F1 → F2 → Prop)
  (match_varinfo : V1 → V2 → Prop)
  (p1 : program F1 V1) (p2 : program F2 V2) : Prop :=
match_program_gen match_fundef match_varinfo p1 p1 p2

lemma match_program_main {F1 V1 F2 V2} [linker F1] [linker V1]
  {match_fundef : program F1 V1 → F1 → F2 → Prop}
  {match_varinfo : V1 → V2 → Prop}
  {p1 : program F1 V1} {p2 : program F2 V2}
  (hm : match_program match_fundef match_varinfo p1 p2) : p2.prog_main = p1.prog_main :=
match_program_gen_main _ _ hm

end linking