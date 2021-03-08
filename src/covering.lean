import category_theory.functor
       category_theory.elements
       displayed
       free

open category_theory is_free_groupoid

variables {C : Type*} [category C] {F : C ⥤ Type*} {X : Type*} [category X]
  (ob : F.elements → X)

-- todo is there a name for this construction? or a way to think about it abstractly?
def homsets {a b : C} (f : a ⟶ b) : Type* :=
Π (s : F.obj a) (t : F.obj b) (h : F.map f s = t), -- this is the data of an arrow over f
  ob ⟨a, s⟩ ⟶ ob ⟨b, t⟩

variable {ob}

lemma homset_hext {a b : C} {p q : a ⟶ b} {P : homsets ob p} {Q : homsets ob q} (h : p = q)
  (hs : ∀ (s : F.obj a), P s _ rfl = Q s _ (by rw h)) : P == Q :=
by { cases h, apply heq_of_eq, funext, cases x_2, apply hs }

-- this is a complete triviality, but it seems we need to state it in order to do dependent
-- rewriting
lemma hs_congr {a b : C} {p : a ⟶ b} (P : homsets ob p) {s s' : F.obj a} {t t' : F.obj b}
  {h : F.map p s = t} (hs : s = s') (ht : t = t') :
    P s t h = eq_to_hom (by rw hs) ≫ P s' t' (by rwa [hs, ht] at h) ≫ eq_to_hom (by rw ht) :=
by { cases hs, cases ht, simp }

variable (ob)

def todo_name_this : disp_cat C :=
{ obj := λ _, unit, 
  mor := λ a b f _ _, homsets ob f,
  id := λ a _ s t h, eq_to_hom (by simp [←h]),
  comp := λ a b c f g _ _ _ F G s t h, F s _ rfl ≫ G _ t (by simp [←h]),
  id_comp := begin
      intros a b _ _ p P,
      apply homset_hext (category.id_comp _),
      intro s,
      rw hs_congr P (functor_to_types.map_id_apply F s) rfl,
      simp,
    end,
  comp_id := begin
      intros a b p _ _ P,
      apply homset_hext (category.comp_id _),
      intro s,
      have : F.map (p ≫ 𝟙 b) s = F.map p s,
      { rw [category.comp_id] },
      rw hs_congr P rfl this,
      simp,
    end,
  assoc := begin
      intros a b c d p q r _ _ _ _ P Q R,
      apply homset_hext (category.assoc _ _ _),
      intro s,
      have : F.map (p ≫ q) s = F.map q (F.map p s),
      { apply functor_to_types.map_comp_apply },
      rw [hs_congr Q rfl this, hs_congr R this rfl],
      simp,
    end }

-- making x functorial is, by design, the same as giving a displayed functor from
-- terminal to todo_name_this
def todo_equiv : functorial ob ≃ disp_functor (𝟭 C) (terminal_disp C) (todo_name_this ob) :=
{ to_fun := λ G,
  { obj := λ a _, (),
    map := λ a b f _ _ _ s t h, G.map' ⟨f, h⟩,
    map_id := begin
      intros a _,
      apply heq_of_eq,
      funext,                      
      have hh : F.map (𝟙 a) s = t := h,
      set S : F.elements := ⟨a, s⟩,
      set T : F.elements := ⟨a, t⟩,
      set H : S ⟶ T := ⟨𝟙 a, hh⟩,
      have ST : S = T,
      { simpa using hh },
      change G.map' H = eq_to_hom (congr_arg ob ST),
      have : eq_to_hom (congr_arg ob ST) = G.map' (eq_to_hom ST),
      { symmetry, apply functorial_eq_to_hom_map },
      rw this,
      congr,
      apply faithful.map_injective (category_of_elements.π F),
      rw eq_to_hom_map,
      refl, -- the above proof would be a lot easier if we could just rewrite along `s = t` in the beginning
    end,
    map_comp := begin
      introsI a b c f g _ _ _ _ _,
      apply heq_of_eq,
      funext,
      change map _ _ = map _ _ ≫ map _ _,
      rw ←functorial.map_comp, refl,
    end },
  inv_fun := λ β,
  { map := λ a b, match a, b with | ⟨a, s⟩, ⟨b, t⟩ :=
      λ f, β.map ((terminal_functorial C).map' f.val).snd s t f.property end,
    map_id' := begin
      rintro ⟨a, s⟩,
      change β.map ((terminal_functorial C).map' (𝟙 a)).snd s s _ = _,
      set A : (terminal_disp C).obj a := (),
      have : ((terminal_functorial C).map' (𝟙 a)).snd = (terminal_disp C).id A,
      { exact unit.ext },
      rw this,
      have foo : β.map ((terminal_disp C).id A) = (todo_name_this ob).id (β.obj A),
      { apply eq_of_heq, apply β.map_id },
      rw foo, refl,
    end,
    map_comp' := begin
      rintros ⟨a, s⟩ ⟨b, t⟩ ⟨c, u⟩ ⟨f, h⟩ ⟨g, j⟩,
      set f' := (terminal_functorial C).map' f,
      set g' := (terminal_functorial C).map' g,
      change β.map ((terminal_functorial C).map' (f ≫ g)).snd s u _
        = β.map f'.snd s t _ ≫ β.map g'.snd t u _,
      transitivity (((todo_name_this ob).comp (β.map f'.snd) (β.map g'.snd)) s u _),
      { repeat {apply congr_fun},
        have : ((terminal_functorial C).map' (f ≫ g)).snd = (terminal_disp C).comp f'.snd g'.snd,
        { exact unit.ext },   
        rw this,
        apply eq_of_heq,
        apply β.map_comp, },
      change _ ≫ _ = _ ≫ _,
      congr,
      { assumption },
      { apply heq_congr_arg₂ (β.map f'.snd s),
        { exact h },
        apply proof_irrel_heq },
      { set fl := λ z Z, β.map g'.snd z u Z,
        change fl _ _ == fl _ _,
        apply heq_congr_arg₂ fl,
        { exact h },
        apply proof_irrel_heq },
  end },
  left_inv := by { intro G, rw functorial_ext, rintros ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩, refl },
  right_inv := begin intro β, ext, { refl }, intros a _, rw heq_iff_eq, rintros ⟨⟩,
    apply heq_of_eq, funext, cases _x, cases _x, cases _x, refl, end }

def name_this_todo {G} [groupoid G] {F : G ⥤ Type*} {X} [groupoid X] (ob : F.elements → X) :
  disp_groupoid G :=
{ inv := λ a b _ _ p P s t h, inv (P t s (by { rw ←h,
      exact (functor_to_types.map_hom_map_inv_apply
        F ((groupoid.iso_equiv_hom _ _).symm p) s) })), -- how to make simp find this?
  inv_comp := begin
      intros a b p _ _ P, 
      apply homset_hext (groupoid.inv_comp _),
      intro s,
      change inv _ ≫ _ = eq_to_hom _,
      have : F.map (groupoid.inv p ≫ p) s = s,
      { rw groupoid.inv_comp, apply functor_to_types.map_id_apply },
      rw hs_congr P rfl this,
      simp,
    end,
  comp_inv := begin
      intros a b p _ _ P, 
      apply homset_hext (groupoid.comp_inv _),
      intro s,
      change _ ≫ inv _ = eq_to_hom _,
      have : F.map (p ≫ groupoid.inv p) s = s,
      { rw groupoid.comp_inv, apply functor_to_types.map_id_apply },
      rw hs_congr P this rfl,
      simp,
    end,
  ..todo_name_this ob }

universe u

-- Given an action of a free groupoid, its category of elements
-- is freely generated by the pullback subquiver.
-- This lemma corresponds to the fact that any covering space of a graph is
-- also a graph. In the HoTT formalization of Nielsen-Schreier, it corresponds
-- to the fact that `coequalizers are stable under pullback'
lemma elements_is_free_groupoid {G} [groupoid.{u u} G] {F : G ⥤ Type u} [is_free_groupoid G] :
  is_free_groupoid F.elements :=
{ gpd_gens := λ x y, { a : gpd_gens x.fst y.fst // F.map (gpd_emb a) x.snd = y.snd },
  gpd_emb := λ x y a, ⟨gpd_emb a, a.property⟩,
  gpd_lift := begin
    introsI X _ f,
    let Y := name_this_todo f.obj,
    set f' : quiver_hom gpd_gens ♯Y.total :=
    { obj := λ x, ⟨x, ()⟩,
      edge := λ a b p, ⟨gpd_emb p, λ s t h, f.edge ⟨p, h⟩⟩ },
    suffices : ∃! y : disp_functor (𝟭 G) (terminal_disp G) Y.to_disp_cat,
      ∀ {c d : G} (p : gpd_gens c d), (f'.edge p).snd = y.map (),
    { refine ((todo_equiv f.obj).exists_unique_congr _).mpr this,
      { exact () },
      { exact () },
      intro y,
      split,
      { intros hyp a b p, funext, apply hyp },
      { rintros hyp ⟨a, s⟩ ⟨b, t⟩ ⟨p, hp⟩,
        change (f'.edge p).snd s t hp = _,
        rw hyp, refl } },
    rcases gpd_lift f' with ⟨P, hP, uP⟩,
    resetI, -- we now perform some trickery to make sure that P maps p to ⟨p, something⟩
    have id_eq : category_theory.functorial_id = functorial_comp f'.obj Y.to_disp_cat.π,
    { rw free_groupoid_ext,
      intros, change _ = (P.map' _).fst,
      rw ←hP, refl },
    have eq_map_fst : ∀ {c d : G} (p : c ⟶ d), p = (P.map' p).fst,
    { intros, change map id p = (functorial_comp f'.obj Y.to_disp_cat.π).map' p,
      rw ←id_eq, refl },
    tactic.unfreeze_local_instances, 
    cases P,
    have : ∃ ma : (Π {c d : G} (p : c ⟶ d), Y.mor p () ()), @P_map = λ x y q, ⟨q, ma q⟩,
    { refine ⟨_, _⟩,
      { intros c d p,
        convert (P_map p).snd,
        apply eq_map_fst },
      funext,
      symmetry,
      apply sigma.ext,
      { apply eq_map_fst },
      { apply eq_mpr_heq } }, 
    rcases this with ⟨P_ma, ⟨⟩⟩, -- trickery accomplished
    set y : disp_functor (𝟭 G) (terminal_disp G) Y.to_disp_cat :=
    { obj := λ _ _, (),
      map := λ a b p a' b' p', P_ma p,
      map_id := λ a a', begin have := P_map_id' a,
        rw [total_id, sigma.ext_iff] at this, exact this.2, end,
      map_comp := λ a b c f g _ _ _ _ _, begin have := P_map_comp' f g,
        rw [total_comp, sigma.ext_iff] at this, exact this.2, end },
    refine ⟨y, _, _⟩,
    { intros a b p, have : f'.edge p = ⟨_, _⟩ := hP p,
      rw sigma.ext_iff at this, apply eq_of_heq, exact this.2 },
    intros z hz,
    cases z,
    have : @z_obj = λ _ _, (),
    { funext, exact unit.ext },
    rcases this with ⟨⟩,
    set P' : functorial f'.obj := {
      map := λ _ _ p, ⟨p, @z_map _ _ p () () ()⟩,
      map_id' := λ _, by { apply sigma.ext, refl, apply z_map_id },
      map_comp' := λ _ _ _ _ _, by { apply sigma.ext, refl, apply z_map_comp } },
    have P'_eq_P := uP P' _,
    { congr,
      apply funext, intro a, apply funext, intro b, apply funext, intro p,
      apply funext, rintro ⟨⟩, apply funext, rintro ⟨⟩, apply funext, rintro ⟨⟩,
      change (P'.map' _).snd = _,
      have : P'.map' p = ⟨p, P_ma p⟩, { rw P'_eq_P, refl },
      rw sigma.ext_iff at this, apply eq_of_heq, exact this.2, },
    intros a b p,
    apply sigma.ext,
    { refl },
    apply heq_of_eq,
    apply hz,
  end
}