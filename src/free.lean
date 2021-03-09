import category_theory.single_obj
       category_theory.functor
       category_theory.elements
       category_theory.action
       quiver
       misc
open category_theory

universes u v

class is_free_group (G) [group.{u} G] :=
(gp_gens : Type u)
(gp_emb : gp_gens → G)
(gp_lift {X} [group.{u} X] (f : gp_gens → X) : ∃! F : G →* X, ∀ a, f a = F (gp_emb a))

class is_free_groupoid (G) [groupoid.{v u} G] :=
(gpd_gens : quiver.{v u} G)
(gpd_emb : Π ⦃a b⦄, gpd_gens a b → (a ⟶ b))
(gpd_lift {X} [group.{v} X] (f : valu gpd_gens X) :
  ∃! F : G ⥤ single_obj X, ∀ {x y : G} (a : gpd_gens x y), f a = F.map (gpd_emb a))
(ind {P : Π {a b : G}, (a ⟶ b) → Prop}
  (base : ∀ a b (e : gpd_gens a b), P (gpd_emb e))
  (id : ∀ a, P (𝟙 a))
  (comp : ∀ a b c (f : a ⟶ b) (g : b ⟶ c), P f → P g → P (f ≫ g))
  (comp : ∀ a b (f : a ⟶ b), P f → P (inv f))
  {a b} (f : a ⟶ b) : P f)

open is_free_group is_free_groupoid

-- this restricted extensionality lemma should be enough for our purposes
lemma is_free_group_ext {G} [group G] [is_free_group G] (f : G →* G) :
  (∀ a : gp_gens G, f (gp_emb a) = gp_emb a) → ∀ g, f g = g :=
begin
  intro hyp,
  suffices : f = monoid_hom.id G,
  { intro g, rw this, refl },
  let F : gp_gens G → G := f ∘ gp_emb,
  rcases gp_lift F with ⟨p, hp, up⟩,
  have : f = p,
  { apply up, intros, refl },
  have : monoid_hom.id G = p,
  { apply up, intros, apply hyp },
  cc,
end

lemma is_free_group_induction {G} [group G] [is_free_group G]
  (P : G → Prop)
  (base : ∀ a, P (gp_emb a))
  (one : P 1)
  (mul : ∀ g h, P g → P h → P (g * h))
  (inv : ∀ g, P g → P (g⁻¹))
  (g : G) : P g :=
let H : subgroup G := { 
  carrier  := P,
  one_mem' := one,
  mul_mem' := mul,
  inv_mem' := inv } in
let f : gp_gens G → H := λ a, ⟨gp_emb a, base a⟩ in
begin
  rcases gp_lift f with ⟨F, hF, _⟩,
  have : ∀ g, H.subtype.comp F g = g,
  { apply is_free_group_ext,
    intro a,
    change (F (gp_emb a)).val = _,
    rw ←hF },
  convert (F g).property,
  symmetry, apply this
end

-- being a free group is an isomorphism invariant
def is_free_group_mul_equiv {G H : Type u} [group G] [group H] [is_free_group G] (h : G ≃* H)
  : is_free_group H :=
{ gp_gens := gp_gens G,
  gp_emb := λ a, h (gp_emb a),
  gp_lift := begin
    introsI X _ f,
    refine (equiv.exists_unique_congr (homset_equiv_of_mul_equiv h) _).mp (gp_lift f),
    intros F, apply forall_congr,
    intro, apply eq.congr,
    { refl },
    { change F _ = F _, simp },
  end }
