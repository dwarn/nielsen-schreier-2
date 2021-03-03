import category_theory.category.Cat category_theory.category.Groupoid

-- this file contains the construction of displayed categories
-- see https://arxiv.org/pdf/1705.04296.pdf

open category_theory

structure displayed_category (C) [category C] :=
(obj  : C → Sort*)
(mor  : Π {a b : C}, (a ⟶ b) → obj a → obj b → Sort*)
(id   : Π {a : C} (x : obj a), mor (𝟙 a) x x)
(comp : Π {a b c : C} {f : a ⟶ b} {g : b ⟶ c}
        {x : obj a} {y : obj b} {z : obj c},
          mor f x y → mor g y z → mor (f ≫ g) x z)
(id_comp : ∀ {a b : C} {x : obj a} {y : obj b} {f : a ⟶ b} (F : mor f x y),
              comp (id x) F == F )
(comp_id : ∀ {a b : C} {x : obj a} {y : obj b} {f : a ⟶ b} (F : mor f x y),
              comp F (id y) == F )
(assoc : ∀ {a b c d : C} {x : obj a} {y : obj b} {z : obj c} {w : obj d}
              {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
                (F : mor f x y) (G : mor g y z) (H : mor h z w),
                  comp (comp F G) H == comp F (comp G H) )

structure displayed_groupoid (G) [groupoid G] extends displayed_category G :=
(inv : Π {a b : G} {x : obj a} {y : obj b} {f : a ⟶ b}, mor f x y → mor (inv f) y x)
(inv_comp : ∀ {a b : G} {x : obj a} {y : obj b} {f : a ⟶ b} (F : mor f x y),
  comp (inv F) F == id y)
(comp_inv : ∀ {a b : G} {x : obj a} {y : obj b} {f : a ⟶ b} (F : mor f x y),
  comp F (inv F) == id x)

-- a displayed category is also a genuine category
def total_category {C} [category C] (D : displayed_category C) : Cat :=
{ α := Σ c : C, D.obj c,
  str := { hom := λ x y, Σ f : x.fst ⟶ y.fst, D.mor f x.snd y.snd,
           id := λ x, ⟨𝟙 x.fst, D.id x.snd⟩,
           comp := λ x y z F G, ⟨F.fst ≫ G.fst, D.comp F.snd G.snd⟩,
           id_comp' := by { intros, apply sigma.ext, apply category.id_comp, apply D.id_comp },
           comp_id' := by { intros, apply sigma.ext, apply category.comp_id', apply D.comp_id },
           assoc' := by { intros, apply sigma.ext, apply category.assoc, apply D.assoc } } }

def total_groupoid {G} [groupoid G] (D : displayed_groupoid G) : Groupoid :=
{ α := (total_category D.to_displayed_category).α,
  str := { inv := λ x y F, ⟨inv F.fst, D.inv F.snd⟩,
           inv_comp' := by { intros, apply sigma.ext, apply groupoid.inv_comp, apply D.inv_comp },
           comp_inv' := by { intros, apply sigma.ext, apply groupoid.comp_inv, apply D.comp_inv }, } }

-- there are a lot of other things we could formalise, maybe the most obvious being the
-- forgetful functor from the total category to C.