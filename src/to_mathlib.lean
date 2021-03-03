import category_theory.single_obj

open category_theory function
universes v v₁ v₂ u u₁ u₂
-- this definition is copied from category_theory.functorial, except we make it a structure
-- rather than a class
@[ext]
structure functorial {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D] 
  (F : C → D) : Type (max v₁ v₂ u₁ u₂) :=
(map       : Π {X Y : C}, (X ⟶ Y) → ((F X) ⟶ (F Y)))
(map_id'   : ∀ (X : C), map (𝟙 X) = 𝟙 (F X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

/-- A functor out of single object category is just a monoid hom -/
def functor_equiv {M C} [monoid M] [category C] (c : C) :
functorial (λ x : single_obj M, c) ≃ (M →* End c) :=
{ to_fun := λ F, { to_fun   := λ (m : End (single_obj.star M)), F.map m,
                   map_one' := F.map_id' _,
                   map_mul' := λ _ _, F.map_comp' _ _ },
  inv_fun := λ f, { map := λ _ _, f,
                    map_id' := λ _, f.map_one,
                    map_comp' := λ _ _ _ _ _, f.map_mul _ _ },
  left_inv := by tidy,
  right_inv := by tidy }

-- two dependent functions out of unit are equal when they agree on ()
-- todo: can we make this @[simp]?
lemma out_of_unit {P : punit.{u} → Type v} {f g : Π a, P a} : 
  f = g ↔ f punit.star = g punit.star :=
begin
  split,
  { cc },
  intro h,
  funext,
  cases x,
  assumption,
end

-- any function out of unit is constant
lemma const_unit_surjective (A) : surjective (λ (a : A) (x : punit.{u}), a) :=
begin
  intro f,
  use f punit.star,
  funext,
  cases x,
  refl, 
end