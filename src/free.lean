import category_theory.single_obj
       category_theory.functor
       category_theory.elements
       category_theory.action
       quiver
       misc
       displayed
open category_theory

universes u v

class is_free_group (G) [group.{u} G] :=
(gp_gens : Type u)
(gp_emb : gp_gens → G)
(gp_lift {X} [group.{u} X] (f : gp_gens → X) : ∃! F : G →* X, ∀ a, f a = F (gp_emb a))

class is_free_groupoid (G) [groupoid.{v u} G] :=
(gpd_gens : quiver.{v u} G)
(gpd_emb : qhom_over_id gpd_gens ♯G)
(gpd_lift {X} [groupoid.{v u} X] (f : quiver_hom gpd_gens ♯X) :
  ∃! F : functorial f.obj, ∀ {x y : G} (a : gpd_gens x y), f.edge a = F.map' (gpd_emb a))

open is_free_group is_free_groupoid

instance free_groupoid_of_free_group (G) [group G] [is_free_group G] : is_free_groupoid (single_obj G) :=
{ gpd_gens := λ _ _, gp_gens G,
  gpd_emb := λ _ _ e, (gp_emb e : G),
  gpd_lift := λ X _ f, begin
    resetI, cases f,
    have : ∃ x : X, f_obj = λ _, x := ⟨_, out_of_unit.mpr rfl⟩,
    rcases this with ⟨x, ⟨⟩⟩,
    let f' : (gp_gens G) → End x := λ a, @f_edge () () a,
    exact ((functorial_equiv x).exists_unique_congr (by tidy)).mpr (gp_lift f'),
  end }

-- a functor out of a free groupoid is determined by its values on the generating subquiver
lemma free_groupoid_ext {G X} [groupoid.{v u} G] [groupoid.{v u} X] [is_free_groupoid G]
   {ob : G → X} {f g : functorial ob} :
  f = g ↔ ∀ (x y : G) (a : gpd_gens x y), f.map' (gpd_emb a) = g.map' (gpd_emb a) :=
begin
  refine ⟨_, _⟩,
  { intros, cc },
  intro h,
  set f' : quiver_hom gpd_gens ♯X := 
    { obj := ob, edge := λ _ _ e, f.map' (gpd_emb e) },
  rcases gpd_lift f' with ⟨p, hp, up⟩,
  have : f = p, { apply up, intros, refl },
  have : g = p, { apply up, intros, apply h },
  cc
end

-- given a predicate on the morphisms of a free group, if we know that it holds on the generators,
-- and on identity morphisms, and is preserved by composition and inverse, then it holds everywhere
lemma free_groupoid_induction {G} [groupoid G] [is_free_groupoid G]
  {P : Π {a b : G}, (a ⟶ b) → Prop}
    (h_id : ∀ a, P (𝟙 a))
    (h_comp : ∀ {a b c} {f : a ⟶ b} {g : b ⟶ c}, P f → P g → P (f ≫ g))
    (h_inv : ∀ {a b} {f : a ⟶ b}, P f → P (inv f))
    (h_base : ∀ {a b : G} (f : gpd_gens a b), P (gpd_emb f))
    : ∀ a b (f : a ⟶ b), P f :=
let subgpd : disp_groupoid G :=
{ obj := λ _ , unit,
  mor := λ _ _ p _ _, plift (P p),
  id := λ a _, plift.up (h_id _),
  comp := λ _ _ _ _ _ _ _ _ p q, plift.up (h_comp p.down q.down),
  inv := λ _ _ _ _ _ p, plift.up (h_inv p.down),
  id_comp  := by { intros, cases F, apply heq_of_eq_mp; simp },
  comp_id  := by { intros, cases F, apply heq_of_eq_mp; simp },
  assoc    := by { intros, cases F, apply heq_of_eq_mp; simp },
  inv_comp := by { intros, cases F, apply heq_of_eq_mp; simp },
  comp_inv := by { intros, cases F, apply heq_of_eq_mp; simp } } in
let F : quiver_hom gpd_gens ♯subgpd.total :=
{ obj := λ a, ⟨a, ()⟩, edge := λ a b p, ⟨gpd_emb p, plift.up $ h_base p⟩ } in
begin
  rcases gpd_lift F with ⟨Q, hQ, _⟩,
  introsI,
  convert (Q.map' f).snd.down,
  change category_theory.functorial_id.map' f = (functorial_comp F.obj subgpd.to_disp_cat.π).map' f,
  congr,
  rw free_groupoid_ext,
  intros x y a,
  change (F.edge _).fst = (Q.map' _).fst,
  rw hQ,
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