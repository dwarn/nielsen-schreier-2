import category_theory.single_obj
       to_mathlib

open category_theory

universes u v

def quiver (G : Type u) := G → G → Type v

def quiver_of_cat (C) [category C] : quiver C := has_hom.hom

structure quiver_hom {G H} (p : quiver G) (q : quiver H) :=
(obj : G → H)
(edge : Π {a b : G}, p a b → q (obj a) (obj b))

def qhom_over_id {G} (p q : quiver G) : Type* :=
Π {a b : G}, p a b → q a b

notation `♯` C := quiver_of_cat C

def quiver_hom_of_functorial {C D} [category C] [category D]
{obj : C → D} (f : functorial obj) : quiver_hom (♯C) (♯D) :=
{ obj := obj,
  edge := f.map }

notation `♮` F := quiver_hom_of_functorial F

def subquiver {G} (p : quiver G) :=
Π a b : G, set (p a b)

def quiver_of_sub {G} {q : quiver G} (p : subquiver q) : quiver G :=
λ a b, { e : q a b // e ∈ p a b }

notation `¡` p := quiver_of_sub p

namespace quiver

inductive path {G} (p : quiver.{u v} G) (a : G) : G → Type (max u v)
| nil  : path a
| cons : Π {b c : G}, path b → p b c → path c

class is_tree {G} [inhabited G] (p : quiver G) :=
(unique_path (b : G) : unique (p.path (default G) b))

attribute [instance] is_tree.unique_path

end quiver

def symmy {G} (p : quiver G) : quiver G :=
λ a b, (p a b) ⊕ (p b a)