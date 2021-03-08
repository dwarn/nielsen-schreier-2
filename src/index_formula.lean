import result
       category_theory.action
       covering

open_locale classical
noncomputable theory

def tree_equiv {G} [inhabited G] (T : quiver G) [is_tree T] :
  T.total ⊕ unit ≃ G :=
{ to_fun := λ x, sum.rec_on x (λ tp, tp.target) (λ _, default G),
  inv_fun := λ g, match g, (default $ T.path (default G) g) with 
                      | _, quiver.path.nil      := sum.inr ()
                      | _, quiver.path.cons p e := sum.inl ⟨_, _, e⟩
                      end,
  left_inv := begin
    intro x,
    rcases x with ⟨a, b, e⟩ | ⟨⟨⟩⟩,
    { dsimp, rw unique.default_eq ((default $ T.path (default G) a).cons e), refl },
    { dsimp, rw unique.default_eq quiver.path.nil, refl }
  end,
  right_inv := begin
    intro g,
    have : ∃ p, default (T.path (default G) g) = p := ⟨_, rfl⟩,
    rcases this with ⟨p, hp⟩,
    dsimp, rw hp,
    cases p; refl
  end }

lemma tree_not_both {G} [inhabited G] (T : quiver G) [is_tree T] {a b : G} (e : T a b) (f : T b a) :
  false :=
begin
  set q : T.path (default G) a := default _,
  have : q = (q.cons e).cons f,
  { apply unique.default_eq },
  apply_fun length at this,
  change length q = length q + 2 at this,
  suffices : 2 = 0,
  { tauto },
  simpa only [self_eq_add_right] using this,
end

def tree_symmy_equiv {G} [inhabited G] {A : quiver.{0 0} G} (T : subquiver (symmy A)) [is_tree ¡T] :
  tree_symmy T ≃ (¡T).total :=
{ to_fun := λ ht, if h : (sum.inl ht.val.edge) ∈ T ht.val.source ht.val.target
                  then ⟨_, _, sum.inl ht.val.edge, h⟩
                  else ⟨_, _, sum.inr ht.val.edge, or.resolve_left ht.property h⟩,
  inv_fun := λ t, match t with
          | ⟨a, b, sum.inl e, h⟩ := ⟨⟨_, _, e⟩, or.inl h⟩
          | ⟨b, a, sum.inr e, h⟩ := ⟨⟨_, _, e⟩, or.inr h⟩
          end,
  left_inv := begin
    rintro ⟨⟨a, b, e⟩, h⟩,
    cases h,
    { dsimp, rw dif_pos h, refl },
    { dsimp, rw dif_neg, { refl },
      intro h2, exact tree_not_both (¡T) ⟨sum.inl e, h2⟩ ⟨sum.inr e, h⟩ }
  end,
  right_inv := begin
    rintro ⟨a, b, e, h⟩,
    cases e,
    { dsimp, rw dif_pos, refl },
    { dsimp, rw dif_neg, { refl }, 
      intro hn, exact tree_not_both (¡T) ⟨sum.inl e, hn⟩ ⟨sum.inr e, h⟩ }
  end }

open quotient_group is_free_group is_free_groupoid category_theory

def action_gens_equiv {G X : Type} [group G] [is_free_group G] [mul_action G X] :
  (gp_gens G) × X ≃ (gpd_gens : quiver (action_category G X)).total :=
{ to_fun := λ p, ⟨⟨(), p.snd⟩, ⟨(), ((gp_emb p.fst) • p.snd : X)⟩, p.fst, rfl⟩,
  inv_fun := λ t, (t.edge, t.source.snd),
  left_inv := by tidy,
  right_inv := begin -- ugh
    intro x, rcases x with ⟨⟨⟨⟩, x⟩, ⟨⟨⟩, y⟩, e, h⟩,
    dsimp, congr, { exact h }, { funext, congr, exact h },
    { exact proof_irrel_heq rfl h }
  end }

def index_formula {G} [group.{0} G] [is_free_group G] (H : subgroup G) :
  (gp_gens G) × (quotient H) ⊕ unit ≃ (gp_gens H) ⊕ (quotient H) :=
calc      (gp_gens G) × (quotient H) ⊕ unit 
        ≃ (gpd_gens : quiver $ action_category G (quotient H)).total ⊕ unit 
            : equiv.sum_congr action_gens_equiv (equiv.refl unit)
    ... ≃ ((gp_gens H) ⊕ tree_symmy _) ⊕ unit
            : equiv.sum_congr (compl_sum_set_equiv _).symm (equiv.refl unit)
    ... ≃ (gp_gens H) ⊕ (tree_symmy (geodesic_subgraph (symmy gpd_gens)) ⊕ _)
            : equiv.sum_assoc _ _ _
    ... ≃ (gp_gens H) ⊕ ((quiver.total _) ⊕ unit)
            : equiv.sum_congr (equiv.refl _) (equiv.sum_congr (tree_symmy_equiv _) (equiv.refl unit))
    ... ≃ (gp_gens H) ⊕ action_category G (quotient H)
            : equiv.sum_congr (equiv.refl _) (tree_equiv _) 
    ... ≃ (gp_gens H) ⊕ quotient H
            : equiv.sum_congr (equiv.refl _) (action_category.obj_equiv G (quotient H)).symm