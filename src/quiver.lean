import category_theory.concrete_category.bundled logic.unique
       category_theory.category.Cat
       category_theory.single_obj
       to_mathlib

open category_theory

universes u v

def quiver (G) := G → G → Type v

def quiver_of_cat (C) [category C] : quiver C := has_hom.hom

def quiver_hom {G H} (p : quiver G) (q : quiver H) (f : G → H) :=
Π ⦃a b : G⦄, p a b → q (f a) (f b)

notation p ` →[` f `] ` q := quiver_hom p q f
notation `♯` C := quiver_of_cat C

def quiver_hom_of_functorial {C D} [category C] [category D]
{f : C → D} (F : functorial f) : ♯C →[f] ♯D :=
F.map

notation `♮` F := quiver_hom_of_functorial F

def id_qhom {G} [p : quiver G] : p →[id] p :=
λ _ _, id

definition quiver_hom_comp {G H K} {p : quiver G} {q : quiver H} {r : quiver K}
{f : G → H} {g : H → K} (F : p →[f] q) (G : q →[g] r) : p →[g ∘ f] r :=
λ a b e, G (F e)

notation G ` ⊚ ` F :80 := quiver_hom_comp F G

def subquiver {G} (p : quiver G) :=
Π a b : G, set (p a b)

def quiver_of_sub {G} {q : quiver G} (p : subquiver q) : quiver G :=
λ a b, { e : q a b // e ∈ p a b }

notation `¡` p := quiver_of_sub p

def sub_hom {G} {q : quiver G} (p : subquiver q) : ¡p →[id] q :=
λ _ _, subtype.val

inductive path {G : Type u} (p : quiver.{v} G) (a : G) : G → Type (max u v)
| nil  : path a
| cons : Π (b c : G), path b → p b c → path c

class is_tree {G : Type u} (p : quiver G) (a : G) :=
(unique_path : Π (b : G), unique (path p a b))

def quiver_sum {G} (p q : quiver G) : quiver G :=
λ a b, p a b ⊕ q a b

def opposite_quiver {G} (p : quiver G) : quiver G :=
flip p

def subquiver_equiv (M) [monoid M] :
  subquiver (♯single_obj M) ≃ set M :=
{ to_fun := λ A, {x | x ∈ A (single_obj.star _) (single_obj.star _)},
  inv_fun := λ A a b, A,
  left_inv := by tidy, right_inv := by tidy }