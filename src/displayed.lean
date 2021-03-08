import category_theory.groupoid
       misc

-- this file contains the construction of displayed categories
-- see https://arxiv.org/pdf/1705.04296.pdf

open category_theory

structure disp_cat (C) [category C] :=
(obj  : C → Type*)  -- ideally these could be Sort*
(mor  : Π {a b : C}, (a ⟶ b) → obj a → obj b → Type*)
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
def disp_cat.total {C} [category C] (D : disp_cat C) := Σ c : C, D.obj c

instance total_displayed {C} [category C] (D : disp_cat C) : category D.total :=
{ hom      := λ x y, Σ f : x.fst ⟶ y.fst, D.mor f x.snd y.snd,
  id       := λ x, ⟨𝟙 x.fst, D.id x.snd⟩,
  comp     := λ x y z F G, ⟨F.fst ≫ G.fst, D.comp F.snd G.snd⟩,
  id_comp' := by { intros, apply sigma.ext, apply category.id_comp, apply D.id_comp },
  comp_id' := by { intros, apply sigma.ext, apply category.comp_id', apply D.comp_id },
  assoc'   := by { intros, apply sigma.ext, apply category.assoc, apply D.assoc } }

lemma total_id {C} [category C] {D : disp_cat C} (x : D.total) :
  𝟙 x = ⟨𝟙 x.fst, D.id x.snd⟩ := rfl

lemma total_comp {C} [category C] {D : disp_cat C} {x y z : D.total} (f : x ⟶ y) (g : y ⟶ z) :
  f ≫ g = ⟨f.fst ≫ g.fst, D.comp f.snd g.snd⟩ := rfl

@[derive category]
def disp_groupoid.total {C} [groupoid C] (D : disp_groupoid C) := D.to_disp_cat.total

instance {C} [groupoid C] (D : disp_groupoid C) : groupoid D.total :=
{ inv := λ x y F, ⟨inv F.fst, D.inv F.snd⟩,
  inv_comp' := by { intros, apply sigma.ext, apply groupoid.inv_comp, apply D.inv_comp },
  comp_inv' := by { intros, apply sigma.ext, apply groupoid.comp_inv, apply D.comp_inv } }

@[ext]
structure disp_functor {C D} [category C] [category D]
  (α : C ⥤ D) (C' : disp_cat C) (D' : disp_cat D) :=
(obj : Π {a : C}, C'.obj a → D'.obj (α.obj a))
(map : Π {a b : C} {f : a ⟶ b} {x : C'.obj a} {y : C'.obj b}, C'.mor f x y → D'.mor (α.map f) (obj x) (obj y))
(map_id : Π {a : C} (x : C'.obj a), map (C'.id x) == D'.id (obj x) . obviously)
(map_comp : Π {a b c : C} {f : a ⟶ b} {g : b ⟶ c} {x : C'.obj a} {y : C'.obj b} {z : C'.obj c}
              (F : C'.mor f x y) (G : C'.mor g y z),
                map (C'.comp F G) == D'.comp (map F) (map G))

def disp_cat.π {C} [category C] (D : disp_cat C) : D.total → C := sigma.fst

instance {C} [category C] (D : disp_cat C) : functorial D.π :=
{ map := λ _ _, sigma.fst }

def terminal_disp (C) [category C] : disp_cat C :=
{ obj  := λ _, unit, -- would be nice to use `true` instead for judgemental proof irrelevance
  mor  := λ _ _ _ _ _, unit,
  id   := λ _ _, (),
  comp := λ _ _ _ _ _ _ _ _ _ _, () }

def terminal_obj (C) [category C] : C → (terminal_disp C).total := λ c, ⟨c, ()⟩

instance terminal_functorial (C) [category C] : functorial (terminal_obj C) :=
{ map := λ a b f, ⟨f, ()⟩ }