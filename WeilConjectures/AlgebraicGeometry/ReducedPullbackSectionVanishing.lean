/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.GenericRank

/-! # Pulling back fibrewise zero sections through a reduced scheme

Source: Stacks Project, Schemes, Tag 01J1 (reduced schemes), applied in a local basis;
Varieties, Tag 0FD6, final paragraph of lemma-bertini.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSection

private theorem frame_coordinate_evaluation_eq_zero
    {X : Scheme.{u}} (M : X.Modules) {W : X.Opens} {J : Type u}
    [Fintype J] [DecidableEq J] (e : M.over W ≅ SheafOfModules.free J)
    {O : X.Opens} (hO : O ≤ W) (m : Γ(M, O)) (x : X) (hx : x ∈ O)
    (hm :
      let : Module (X.presheaf.stalk x) (X.residueField x) :=
        Module.compHom _ (X.residue x).hom
      (M.presheaf.germ O x hx m ⊗ₜ[X.presheaf.stalk x]
        (1 : X.residueField x)) = 0) (j : J) :
    X.evaluation O x hx (sectionsLinearEquivOfOverIsoFree e hO m j) = 0 := by
  let : Module (X.presheaf.stalk x) (X.residueField x) :=
    Module.compHom _ (X.residue x).hom
  obtain ⟨b, hb⟩ := exists_basis_stalk_of_over_iso_free e (hO hx)
  have hc : b.coord j (M.presheaf.germ O x hx m) =
      X.presheaf.germ O x hx (sectionsLinearEquivOfOverIsoFree e hO m j) := by
    conv_lhs => rw [eq_sum_smul_frameSection e hO m, map_sum]
    simp_rw [germ_smul, TopCat.Presheaf.germ_res_apply, ← hb]
    simp [Finsupp.single_apply]
  have h := congrArg
    (fun v ↦ TensorProduct.lid (X.presheaf.stalk x) (X.residueField x)
      (TensorProduct.map (b.coord j) LinearMap.id v)) hm
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
    map_zero, hc] at h
  change (X.residue x) (X.presheaf.germ O x hx
    (sectionsLinearEquivOfOverIsoFree e hO m j)) * 1 = 0 at h
  simpa only [mul_one, Scheme.evaluation, CommRingCat.comp_apply] using h

private theorem pullback_frame_section_eq_zero
    {X R T : Scheme.{u}} [IsReduced R] (i : R ⟶ X) (g : T ⟶ R)
    (M : X.Modules) {W : X.Opens} {J : Type u} [Finite J]
    (e : M.over W ≅ SheafOfModules.free J)
    {O : X.Opens} (hO : O ≤ W) (m : Γ(M, O))
    (hm : ∀ (r : R) (hr : i r ∈ O),
      letI : Module (X.presheaf.stalk (i r)) (X.residueField (i r)) :=
        Module.compHom _ (X.residue (i r)).hom
      (M.presheaf.germ O (i r) hr m ⊗ₜ[X.presheaf.stalk (i r)]
        (1 : X.residueField (i r))) = 0) :
    tensorPullbackSection (g ≫ i) M O m = 0 := by
  classical
  let := Fintype.ofFinite J
  have hc (j : J) : i.app O (sectionsLinearEquivOfOverIsoFree e hO m j) = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    apply (R.basicOpen_eq_bot_iff_forall_evaluation_eq_zero _).mpr
    intro r
    rw [← Scheme.evaluation_naturality_apply i r r.property,
      frame_coordinate_evaluation_eq_zero M e hO m (i r) r.property (hm r r.property) j,
      map_zero]
  have hcomp (j : J) :
      (g ≫ i).app O (sectionsLinearEquivOfOverIsoFree e hO m j) = 0 := by
    change g.app (i ⁻¹ᵁ O) (i.app O _) = 0
    rw [hc, map_zero]
  let adj := tensorPullbackSectionAdjunction (g ≫ i)
  have hunit : ∀ (N : X.Modules) (B : X.Opens) (n : Γ(N, B)),
      (adj.unit.app N).app B n = tensorPullbackSection (g ≫ i) N B n :=
    (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction (g ≫ i))).1
  rw [← hunit, eq_sum_smul_frameSection e hO m, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [Hom.app_smul, hunit]
  change (g ≫ i).app O (sectionsLinearEquivOfOverIsoFree e hO m j) •
    tensorPullbackSection (g ≫ i) M O (M.presheaf.map (homOfLE hO).op (frameSection e j)) = 0
  rw [hcomp, zero_smul]

/-- A section of a finite locally free module whose ambient residue values vanish on a
reduced scheme pulls back to zero through that scheme, even after a nonreduced base change.

Source: Stacks Project, Schemes, Tag 01J1 (sections on a reduced scheme);
Sheaves of Modules, local free-module calculation; used in Varieties, Tag 0FD6.
(blueprint: lem-zl-reduced-pullback-section-vanishing).

Proof: Cover the source open by opens trivializing M. In each basis write m as a finite
column of regular functions. Vanishing in the ambient residue fibre means that every
coordinate evaluates to zero at i(r). The local ring map to the stalk at r, followed by
its residue map, factors through that ambient residue field. Thus each pulled-back
coordinate vanishes in every residue field of the reduced inverse-image open in R.
Its zero locus is the entire open, so it belongs to the nilradical; reducedness makes
it zero. The composite pullback of every coordinate is zero by functoriality of ring sections.
The section-normalized tensor-pullback unit is additive and semilinear, so the local
frame expansion pulls back to a sum of zero multiples. Germ extensionality gives the
claim on V. No reducedness of T, affineness, or nonemptiness is
required; a module of rank zero and an empty open obey the same calculation. -/
theorem tensorPullbackSection_eq_zero_of_reduced_factor
    {X R T : Scheme.{u}} [IsReduced R] (i : R ⟶ X) (g : T ⟶ R)
    (M : X.Modules) [M.IsFiniteLocallyFree] (U : X.Opens) (m : Γ(M, U))
    (hm : ∀ (r : R) (hr : i r ∈ U),
      letI : Module (X.presheaf.stalk (i r)) (X.residueField (i r)) :=
        Module.compHom (X.residueField (i r)) (X.residue (i r)).hom
      (M.presheaf.germ U (i r) hr m ⊗ₜ[X.presheaf.stalk (i r)]
        (1 : X.residueField (i r))) = 0)
    (V : T.Opens) (hV : V ≤ (g ≫ i) ⁻¹ᵁ U) :
    ((tensorPullback (g ≫ i)).obj M).presheaf.map (homOfLE hV).op
      (tensorPullbackSection (g ≫ i) M U m) = 0 := by
  classical
  let h := g ≫ i
  let N := (tensorPullback h).obj M
  let adj := tensorPullbackSectionAdjunction h
  have hunit : ∀ (B : X.Opens) (n : Γ(M, B)),
      (adj.unit.app M).app B n = tensorPullbackSection h M B n :=
    (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction h)).1 M
  apply TopCat.Presheaf.section_ext ⟨N.presheaf, N.isSheaf⟩
  intro t ht
  change N.presheaf.germ V t ht _ = _
  rw [map_zero, TopCat.Presheaf.germ_res_apply]
  obtain ⟨W, J, _, hW, ⟨e⟩⟩ := exists_mem_over_iso_free M (h t)
  let O := U ⊓ W
  have hOU : O ≤ U := inf_le_left
  have hOW : O ≤ W := inf_le_right
  have htO : h t ∈ O := ⟨hV ht, hW⟩
  let mO := M.presheaf.map (homOfLE hOU).op m
  have hmO (r : R) (hr : i r ∈ O) :
      letI : Module (X.presheaf.stalk (i r)) (X.residueField (i r)) :=
        Module.compHom _ (X.residue (i r)).hom
      (M.presheaf.germ O (i r) hr mO ⊗ₜ[X.presheaf.stalk (i r)]
        (1 : X.residueField (i r))) = 0 := by
    simpa only [mO, TopCat.Presheaf.germ_res_apply] using hm r hr.1
  have hz := pullback_frame_section_eq_zero i g M e hOW mO hmO
  have hn := Hom.app_presheaf_map (adj.unit.app M) (homOfLE hOU) m
  change (adj.unit.app M).app O mO =
    N.presheaf.map (homOfLE (h.preimage_mono hOU)).op ((adj.unit.app M).app U m) at hn
  rw [hunit, hunit] at hn
  rw [← TopCat.Presheaf.germ_res_apply N.presheaf
    (homOfLE (h.preimage_mono hOU)) t htO, ← hn, hz, map_zero]

end AlgebraicGeometry.Scheme.Modules
