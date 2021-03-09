import arborescence contract connected covering

noncomputable theory

open category_theory

instance end_is_free {G} [groupoid G] [inhabited G] [preconnected_groupoid G] [is_free_groupoid G] :
  is_free_group (End (default G)) :=
contract (geodesic_subgraph _)

instance subgroup_is_free {G} [group G] [is_free_group G] (H : subgroup G) :
  is_free_group H :=
is_free_group_mul_equiv (End_mul_equiv_subgroup H)