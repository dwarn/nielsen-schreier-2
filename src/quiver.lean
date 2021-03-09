import category_theory.single_obj
       misc

open category_theory

universes v u

def quiver (G : Type u) := G → G → Type v

def valu {G} (p : quiver G) (X) :=
Π {a b}, p a b → X

def subquiver {G} (p : quiver G) :=
Π a b : G, set (p a b)

def quiver_of_sub {G} {q : quiver G} (p : subquiver q) : quiver G :=
λ a b, { e : q a b // e ∈ p a b }

notation `¡` p := quiver_of_sub p

namespace quiver

@[ext]
structure total {G} (q : quiver G) :=
(source : G)
(target : G)
(edge : q source target)

inductive path {G} (p : quiver.{u v} G) (a : G) : G → Type (max u v)
| nil  : path a
| cons : Π {b c : G}, path b → p b c → path c

end quiver

class is_arbor {G} [inhabited G] (p : quiver G) :=
(unique_path (b : G) : unique (p.path (default G) b))

attribute [instance] is_arbor.unique_path

def symmy {G} (p : quiver G) : quiver G :=
λ a b, (p a b) ⊕ (p b a)

def tree_symmy {G} [inhabited G] {p : quiver.{v u} G} (t : subquiver (symmy p)) [is_arbor ¡t] :
  set p.total :=
{ tp | sum.inl tp.edge ∈ t tp.source tp.target ∨ sum.inr tp.edge ∈ t tp.target tp.source }
