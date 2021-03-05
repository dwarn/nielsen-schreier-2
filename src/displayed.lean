import category_theory.category.Cat category_theory.category.Groupoid to_mathlib

-- this file contains the construction of displayed categories
-- see https://arxiv.org/pdf/1705.04296.pdf

open category_theory

structure disp_cat (C) [category C] :=
(obj  : C → Sort*) 
(mor  : Π {a b : C}, (a ⟶ b) → obj a → obj b → Sort*)
(id   : Π {a : C} (x : obj a), mor (𝟙 a) x x)
(comp : Π {a b c : C} {f : a ⟶ b} {g : b ⟶ c}
        {x : obj a} {y : obj b} {z : obj c},
          mor f x y → mor g y z → mor (f ≫ g) x z)
(id_comp : ∀ {a b : C} {f : a ⟶ b} {x : obj a} {y : obj b} (F : mor f x y),
              comp (id x) F == F . obviously )
(comp_id : ∀ {a b : C} {f : a ⟶ b} {x : obj a} {y : obj b} (F : mor f x y),
              comp F (id y) == F . obviously )
(assoc : ∀ {a b c d : C} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
            {x : obj a} {y : obj b} {z : obj c} {w : obj d}
              (F : mor f x y) (G : mor g y z) (H : mor h z w),
                comp (comp F G) H == comp F (comp G H) . obviously )

structure disp_groupoid (G) [groupoid G] extends disp_cat G :=
(inv : Π {a b : G} {x : obj a} {y : obj b} {f : a ⟶ b}, mor f x y → mor (inv f) y x)
(inv_comp : ∀ {a b : G} {f : a ⟶ b} {x : obj a} {y : obj b} (F : mor f x y),
  comp (inv F) F == id y . obviously)
(comp_inv : ∀ {a b : G} {f : a ⟶ b} {x : obj a} {y : obj b} (F : mor f x y),
  comp F (inv F) == id x . obviously)

-- a displayed category is also a genuine category
def disp_cat.total {C} [category C] (D : disp_cat C) : Cat :=
{ α := Σ c : C, D.obj c,
  str := { hom      := λ x y, Σ f : x.fst ⟶ y.fst, D.mor f x.snd y.snd,
           id       := λ x, ⟨𝟙 x.fst, D.id x.snd⟩,
           comp     := λ x y z F G, ⟨F.fst ≫ G.fst, D.comp F.snd G.snd⟩,
           id_comp' := by { intros, apply sigma.ext, apply category.id_comp, apply D.id_comp },
           comp_id' := by { intros, apply sigma.ext, apply category.comp_id', apply D.comp_id },
           assoc'   := by { intros, apply sigma.ext, apply category.assoc, apply D.assoc } } }

def disp_groupoid.total {G} [groupoid G] (D : disp_groupoid G) : Groupoid :=
{ α := D.to_disp_cat.total.α,
  str := { inv       := λ x y F, ⟨inv F.fst, D.inv F.snd⟩,
           inv_comp' := by { intros, apply sigma.ext, apply groupoid.inv_comp, apply D.inv_comp },
           comp_inv' := by { intros, apply sigma.ext, apply groupoid.comp_inv, apply D.comp_inv }, } }

@[ext]
structure disp_functor {C D} [category C] [category D]
  (α : C ⥤ D) (C' : disp_cat C) (D' : disp_cat D) :=
(obj : Π {a : C}, C'.obj a → D'.obj (α.obj a))
(map : Π {a b : C} {f : a ⟶ b} {x : C'.obj a} {y : C'.obj b}, C'.mor f x y → D'.mor (α.map f) (obj x) (obj y))
(map_id : Π {a : C} (x : C'.obj a), map (C'.id x) == D'.id (obj x) . obviously)
(map_comp : Π {a b c : C} {f : a ⟶ b} {g : b ⟶ c} {x : C'.obj a} {y : C'.obj b} {z : C'.obj c}
              (F : C'.mor f x y) (G : C'.mor g y z),
                map (C'.comp F G) == D'.comp (map F) (map G))

def disp_cat.π {C} [category C] (D : disp_cat C) :
  functorial (λ x : D.total, x.fst) :=
{ map := λ _ _, sigma.fst }

def terminal_disp (C) [category C] : disp_cat C :=
{ obj  := λ _, unit, -- would be nice to use `true` instead for judgemental proof irrelevance
  mor  := λ _ _ _ _ _, unit,
  id   := λ _ _, (),
  comp := λ _ _ _ _ _ _ _ _ _ _, () }

def terminal_functorial (C) [category C] : @functorial C _ _ (terminal_disp C).total.str (λ c, ⟨c, ()⟩) :=
{ map := λ a b f, ⟨f, ()⟩ }

-- given a section of the projection functor which is strict on objects,
-- make it strict also on morphisms
lemma strictify_map {C} [category C] {D : disp_cat C}
  {ob : Π c : C, D.obj c} {f : @functorial C _ _ D.total.str (λ c, ⟨c, ob c⟩)}
  (h : functorial_comp f D.π = functorial_id C) :
    ∃ (ma : Π {c d : C} (p : c ⟶ d), D.mor p (ob c) (ob d)),
      f.map = (λ c d p, ⟨p, ma p⟩) :=
begin
  refine ⟨_, _⟩,
  { intros c d p,
    convert (f.map p).snd,
    change p = (functorial_comp f $ disp_cat.π D).map p,
    rw h, refl },
  funext,
  apply sigma.ext,
  { change (functorial_comp f $ disp_cat.π D).map x_2 = x_2,
    rw h, refl },
  symmetry, simp, --??
end