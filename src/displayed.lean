import category_theory.category.Cat

-- this file contains the construction of displayed categories
-- see https://arxiv.org/pdf/1705.04296.pdf

open category_theory

variables (C : Type*) [category C]

structure displayed_category :=
(obj  : C → Type*)
(mor  : Π {a b : C}, (a ⟶ b) → obj a → obj b → Type*)
(id   : Π {a : C} (x : obj a), mor (𝟙 a) x x)
(comp : Π {a b c : C} {f : a ⟶ b} {g : b ⟶ c}
        {x : obj a} {y : obj b} {z : obj c},
          mor f x y → mor g y z → mor (f ≫ g) x z)
(comp_id : ∀ {a b : C} {x : obj a} {y : obj b} {f : a ⟶ b} (F : mor f x y),
              comp F (id y) == F )
(id_comp : ∀ {a b : C} {x : obj a} {y : obj b} {f : a ⟶ b} (F : mor f x y),
              comp (id x) F == F )
(assoc : ∀ {a b c d : C} {x : obj a} {y : obj b} {z : obj c} {w : obj d}
              {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
                (F : mor f x y) (G : mor g y z) (H : mor h z w),
                  comp (comp F G) H == comp F (comp G H) )

variable {C}

-- a displayed category is also a genuine category
def total_category (D : displayed_category C) : Cat :=
{ α := Σ c : C, D.obj c,
  str := { hom := λ x y, Σ f : x.fst ⟶ y.fst, D.mor f x.snd y.snd,
           id := λ x, ⟨𝟙 x.fst, D.id x.snd⟩,
           comp := λ x y z F G, ⟨F.fst ≫ G.fst, D.comp F.snd G.snd⟩,
           id_comp' := by { intros, apply sigma.ext, { simp }, apply D.id_comp },
           comp_id' := by { intros, apply sigma.ext, { simp }, apply D.comp_id },
           assoc' := by { intros, apply sigma.ext, { simp }, apply D.assoc } } }
           -- probably the above proofs would be tidy if D has correct simp attributes

-- there are a lot of other things we could formalise, maybe the most obvious being the
-- forgetful functor from the total category to C.