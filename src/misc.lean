import category_theory.single_obj 
       category_theory.functorial
       category_theory.action

open category_theory function quotient_group
universes v v₁ v₂ u u₁ u₂

lemma functorial_eq_to_hom_map {C D} [category C] [category D] (f : C → D) [functorial f] {X Y : C}
  (p : X = Y) : map f (eq_to_hom p) = eq_to_hom (congr_arg f p) :=
by { cases p, exact functorial.map_id }

instance {C} [category C] (F : C ⥤ Type*) : faithful (category_of_elements.π F) := 
by tidy

lemma heq_congr_arg₂ {A : Sort u} {P Q : A → Sort*} (f : Π a, P a → Q a) :
∀ a b c d, a = b → c == d → f a c == f b d :=
by cc

def equiv.set.congr.equiv {A B} (h : A ≃ B) (s : set A) : s ≃ (equiv.set.congr h s) :=
{ to_fun := λ x, ⟨h x.val, ⟨_, x.property, rfl⟩⟩,
  inv_fun := λ y, ⟨h.symm y, by { have : y.val ∈ _ '' _ := y.property,
              rw h.image_eq_preimage at this,
              exact this, }⟩,
  left_inv := by tidy,
  right_inv := by tidy }

def homset_equiv_of_mul_equiv {G H K} [group G] [group H] [group K] (h : G ≃* H) :
  (G →* K) ≃ (H →* K) :=
{ to_fun := λ g, monoid_hom.comp g h.symm.to_monoid_hom,
  inv_fun := λ g, monoid_hom.comp g h.to_monoid_hom,
  left_inv := by tidy,
  right_inv := by tidy }

lemma stabilizer_of_coset_action {G} [group G] {H : subgroup G} :
  mul_action.stabilizer G (default _ : quotient H) = H :=
by { ext, change _ = _ ↔ _, rw eq_comm, convert quotient_group.eq, simp }

lemma out_of_unit {P : punit.{u} → Type v} {f g : Π a, P a} :
  f = g ↔ f punit.star = g punit.star :=
by tidy

-- we are going against the grain by trying to use `functorial` in a non-class way
def category_theory.functorial.map' {C D} [category C] [category D] {ob : C → D} (F : functorial ob)
  {x y : C} : (x ⟶ y) → (ob x ⟶ ob y) := @functorial.map C _ D _ ob F x y

lemma functorial_ext {C D} [category C] [category D] (ob : C → D) :
  ∀ (f g : functorial ob), f = g ↔ ∀ (x y : C) (p : x ⟶ y), f.map' p = g.map' p :=
begin
  intros f g,
  refine ⟨by cc, _⟩,
  { intro h, cases f, cases g, congr, funext, apply h }
end

/-- A functor out of single object category is just a monoid hom -/
def functorial_equiv {M C} [monoid M] [category C] (c : C) :
functorial (λ x : single_obj M, c) ≃ (M →* End c) :=
{ to_fun := by { introI F, exact { to_fun   := λ (m : End (single_obj.star M)), map (λ _, c) m,
                   map_one' := functorial.map_id,
                   map_mul' := λ _ _, functorial.map_comp' _ _ } },
  inv_fun := λ f, { map := λ _ _, f,
                    map_id' := λ _, f.map_one,
                    map_comp' := λ _ _ _ _ _, f.map_mul _ _ },
  left_inv := by { intro x, rw functorial_ext, rintros ⟨⟩ ⟨⟩ _, refl },
  right_inv := by tidy }

instance action_category_inhabited {M X} [monoid M] [mul_action M X] [inhabited X] :
  inhabited (action_category M X) := ⟨⟨single_obj.star M, (default _ : X)⟩⟩

def End_mul_equiv_subgroup {G} [group G] (H : subgroup G) : 
  End (default (action_category G $ quotient H)) ≃* H := 
begin
  refine mul_equiv.trans _ _,
  { exact mul_action.stabilizer G (default _ : quotient H) },
  { apply_instance },
  { apply mul_equiv.refl }, -- this is a heavy refl
  { rw stabilizer_of_coset_action },
end