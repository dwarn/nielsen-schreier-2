import category_theory.single_obj 
       category_theory.action

open_locale classical
open category_theory function quotient_group
universes v v₁ v₂ u u₁ u₂

instance {C} [category C] (F : C ⥤ Type*) : faithful (category_of_elements.π F) := 
by tidy

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

instance action_category_inhabited {M X} [monoid M] [mul_action M X] [inhabited X] :
  inhabited (action_category M X) := ⟨⟨single_obj.star M, (default _ : X)⟩⟩

def End_mul_equiv_subgroup {G} [group G] (H : subgroup G) : 
  End (default (action_category G (quotient H))) ≃* H := 
begin
  refine mul_equiv.trans _ _,
  { exact mul_action.stabilizer G (default _ : quotient H) },
  { apply_instance },
  { apply mul_equiv.refl }, -- this is a heavy refl
  { rw stabilizer_of_coset_action },
end

noncomputable def compl_sum_set_equiv {A} (s : set A) : (set.compl s) ⊕ s ≃ A :=
{ to_fun := λ x, sum.rec_on x coe coe,
  inv_fun := λ a, if h : a ∈ s
                  then sum.inr ⟨a, h⟩
                  else sum.inl ⟨a, h⟩,
  left_inv := begin
    intro x,
    rcases x with ⟨x, h⟩ | ⟨x, h⟩,
    { dsimp, rw dif_neg },
    { dsimp, rw dif_pos }
  end,
  right_inv := begin
    intro y, by_cases y ∈ s,
    { dsimp, rw dif_pos, { refl }, exact h }, 
    { dsimp, rw dif_neg, { refl }, exact h }, 
  end }

instance (G A X : Type*) [group G] [mul_action G A] : mul_action G (A → X) :=
{ smul := λ g F a, F (g⁻¹ • a), -- the inverse is only here so we get a *left* action
  one_smul := by tidy,
  mul_smul := by simp [mul_smul] }

def my_mul_aut (G A X : Type*) [group G] [mul_action G A] [group X] :
  G →* mul_aut (A → X) :=
{ to_fun := λ g, 
  { to_fun := λ F, g • F,
    inv_fun := λ F, g⁻¹ • F,
    left_inv := λ F, inv_smul_smul g F,
    right_inv := λ F, smul_inv_smul g F,
    map_mul' := by tidy },
  map_one' := by tidy,
  map_mul' := by { intros, ext, simp [mul_smul] }}