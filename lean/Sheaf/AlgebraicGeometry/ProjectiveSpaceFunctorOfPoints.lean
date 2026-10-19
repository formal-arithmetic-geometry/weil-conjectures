/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardChartsNonvanishing
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-!
# Projective space as a functor of points

Source: literature/stacks-project/constructions.tex, Lemma 27.13.1 (Tag 01NE)
(blueprint: lem-weil-pbc-projective-space-functor-of-points)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

set_option hygiene false in
local notation "P" n:max => ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of (ULift.{u} ℤ)))
set_option hygiene false in
local notation "O" n:max => ProjectiveSpace.twist
  (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of (ULift.{u} ℤ))) 1
set_option hygiene false in
local notation "T" n:max i:max => ProjectiveSpace.twistOneSection
  (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of (ULift.{u} ℤ))) (ULift.up i)
set_option hygiene false in
local notation "pb" f:max M:max s:max => (((Classical.choose
  (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app M).val.app (Opposite.op ⊤) s)

open Scheme.Modules ProjectiveSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComparison_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    (((Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (pullbackPushforwardAdjunction f)).app M).hom.app ⊤ (pb f M s) =
        pullbackSection f s := by
  exact congrArg (fun t ↦ t.val.app (Opposite.op ⊤) s)
    ((Classical.choose (exists_tensorPullbackAdjunction f)).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction f) M)

open Scheme.Modules ProjectiveSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorPullback_section_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (a : M ⟶ N) (s : Γ(M, ⊤)) :
    ((tensorPullback f).map a).app ⊤ (pb f M s) = pb f N (a.app ⊤ s) := by
  exact congrArg (fun t ↦ t.val.app (Opposite.op ⊤) s)
    ((Classical.choose (exists_tensorPullbackAdjunction f)).unit_naturality a)

open Scheme.Modules ProjectiveSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projective_pair_injective {I : Type u} {Y S : Scheme.{u}} [IsAffine S]
    {L : Y.Modules} (s : I → Γ(L, ⊤)) {ψ χ : Y ⟶ ℙ(I; S)}
    (a : twistRestrict ψ 1 ≅ L) (b : twistRestrict χ 1 ≅ L)
    (ha : ∀ i, a.hom.app ⊤ (pullbackSection ψ (twistOneSection I S i)) = s i)
    (hb : ∀ i, b.hom.app ⊤ (pullbackSection χ (twistOneSection I S i)) = s i)
    (hbase : ψ ≫ ℙ(I; S) ↘ S = χ ≫ ℙ(I; S) ↘ S) : ψ = χ := by
  have ha' (i) : a.hom.app _ (pullbackSection ψ (twistOneSection I S i)) =
      L.presheaf.map (homOfLE (le_top : ψ ⁻¹ᵁ ⊤ ≤ ⊤)).op (s i) := by
    simpa only [Scheme.Hom.preimage_top, presheaf_map_id_apply] using ha i
  have hb' (i) : b.hom.app _ (pullbackSection χ (twistOneSection I S i)) =
      L.presheaf.map (homOfLE (le_top : χ ⁻¹ᵁ ⊤ ≤ ⊤)).op (s i) := by
    simpa only [Scheme.Hom.preimage_top, presheaf_map_id_apply] using hb i
  let U (i : I) : Y.Opens := ψ ⁻¹ᵁ standardOpen I S i
  have hU : ⨆ i, U i = ⊤ := ψ.iSup_preimage_eq_top (iSup_standardOpen I S)
  have hχ (i : I) : U i = χ ⁻¹ᵁ standardOpen I S i := by
    dsimp only [U]
    rw [← generatingLocus_eq_preimage_standardOpen a.hom ha',
      generatingLocus_eq_preimage_standardOpen b.hom hb']
  apply Scheme.Opens.hom_ext_of_iSup_eq_top U hU
  intro i
  have hψi : ((U i).ι ≫ ψ) ⁻¹ᵁ standardOpen I S i = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ x.2
  have hχi : ((U i).ι ≫ χ) ⁻¹ᵁ standardOpen I S i = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ (show x.1 ∈ χ ⁻¹ᵁ standardOpen I S i from (hχ i) ▸ x.2)
  apply hom_ext_of_preimage_standardOpen_eq_top i hψi hχi
    (by simpa only [Category.assoc] using congrArg ((U i).ι ≫ ·) hbase)
  intro j
  have hratio : ψ.appLE (standardOpen I S i) (U i) le_rfl (coordRatio I S i j) =
      χ.appLE (standardOpen I S i) (U i) (hχ i).le (coordRatio I S i j) := by
    apply (isFreeGenerator_of_twistRestrict_iso a.hom ha' i).smul_left_injective
    have h₁ := map_eq_coordRatio_smul_of_twistRestrict_iso a.hom ha' i j
    have h₂ := congrArg (L.presheaf.map (homOfLE (hχ i).le).op)
      (map_eq_coordRatio_smul_of_twistRestrict_iso b.hom hb' i j)
    simp only [Scheme.Modules.map_smul, presheaf_map_homOfLE_map_homOfLE] at h₂
    have hid (r : Γ(Y, ψ ⁻¹ᵁ standardOpen I S i)) :
        Y.presheaf.map (homOfLE le_rfl).op r = r :=
      Scheme.presheaf_map_id_apply (homOfLE le_rfl) r
    simpa only [Scheme.Hom.appLE, CommRingCat.comp_apply, U, hid] using h₁.symm.trans h₂
  have e₁ : ((U i).ι ≫ ψ).appLE (standardOpen I S i) ⊤ hψi.ge
      (coordRatio I S i j) =
      (U i).ι.appLE (U i) ⊤ (fun x _ ↦ x.2)
        (ψ.appLE (standardOpen I S i) (U i) le_rfl (coordRatio I S i j)) := by
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have e₂ : ((U i).ι ≫ χ).appLE (standardOpen I S i) ⊤ hχi.ge
      (coordRatio I S i j) =
      (U i).ι.appLE (U i) ⊤ (fun x _ ↦ x.2)
        (χ.appLE (standardOpen I S i) (U i) (hχ i).le (coordRatio I S i j)) := by
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [e₁, e₂, hratio]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
-- Comparing the two explicit module pullbacks needs additional elaboration heartbeats.
/-- The universal pair on integral projective space and its classification of all
invertible modules with fibrewise generating sections. The first clause says that
pulling back the universal pair always gives such a pair; the second classifies them
uniquely up to section-preserving isomorphism. The last clause asserts compatibility
with pullback. Equivalence invariance and injectivity on equivalence classes follow
from the same unique classification; surjectivity is the first clause with identity
isomorphism. Thus these clauses give the stated representing functor.

`P n` is `ℙ^n_ℤ = ℙ(Fin (n+1); Spec ℤ)` (def-nagata-projective-space-base-change over
`Spec ℤ`), `O n` its twisting sheaf `twist _ _ 1` (def-pc-projective-space-twist) and
`T n i` the coordinate section `twistOneSection _ _ i`; `pb f M s` is the pullback of a
global section along the unit of `exists_tensorPullbackAdjunction f`.

Source: Stacks Project, Constructions, Lemma 27.13.1 (Tag 01NE), via 01NA and 01N9
(blueprint: lem-weil-pbc-projective-space-functor-of-points).

Proof:
1. The standard charts cover projective space, and each coordinate trivializes O(1)
   there (prop-nagata-proj-standard-open and the twisting-sheaf-charts node).
2. Nonvanishing-section-trivializes gives the opens Y_s and the ratios s_l/s_j;
   invertible-generating-sections-fibre shows that these opens cover Y.
3. The ratios give ring maps from each affine chart and hence local morphisms by
   morphism-into-affine-scheme.
4. The ratio identities show agreement on overlaps, by equality on chart generators.
5. Scheme-morphism-gluing gives the global morphism and its chart inverse images.
6. The local trivializations sending pulled-back coordinates to s_i agree and glue
   to an isomorphism, by invertible-pullback-invertible and sheaf-hom-is-sheaf.
7. Any other morphism has the same chart inverse images and the same ratios;
   morphism-into-affine-scheme and scheme-morphism-gluing give uniqueness.
8. Section-preserving isomorphisms preserve this morphism by uniqueness, and every
   morphism yields a generating pulled-back pair (invertible-pullback-tensor).
9. Pulling back the isomorphism gives the composite's pair via the canonical
   composition isomorphism (invertible-pullback-tensor). Uniqueness proves naturality;
   the classification is bijective on equivalence classes, hence representable. -/
theorem projectiveSpace_functor_of_points (n : ℕ) :
    (∀ (Y : Scheme.{u}) (ψ : Y ⟶ P n),
      ((Scheme.Modules.tensorPullback ψ).obj (O n)).IsInvertible ∧
      ∀ y : Y, ∃ i : Fin (n + 1), y ∈ Scheme.Modules.nonvanishingLocus
        ((Scheme.Modules.tensorPullback ψ).obj (O n)) (pb ψ (O n) (T n i))) ∧
    (∀ (Y : Scheme.{u}) (L : Y.Modules) [L.IsInvertible]
      (s : Fin (n + 1) → (Γ(L, ⊤) : Type u)),
      (∀ y : Y, ∃ i, y ∈ Scheme.Modules.nonvanishingLocus L (s i)) →
      ∃! ψ : Y ⟶ P n,
        ∃ e : (Scheme.Modules.tensorPullback ψ).obj (O n) ≅ L,
          ∀ i, e.hom.app ⊤ (pb ψ (O n) (T n i)) = s i) ∧
    (∀ (Y Y' : Scheme.{u}) (h : Y' ⟶ Y) (ψ : Y ⟶ P n)
      (L : Y.Modules) (s : Fin (n + 1) → (Γ(L, ⊤) : Type u))
      (e : (Scheme.Modules.tensorPullback ψ).obj (O n) ≅ L),
      (∀ i, e.hom.app ⊤ (pb ψ (O n) (T n i)) = s i) →
      ∃ e' : (Scheme.Modules.tensorPullback (h ≫ ψ)).obj (O n) ≅
          (Scheme.Modules.tensorPullback h).obj L,
        ∀ i, e'.hom.app ⊤ (pb (h ≫ ψ) (O n) (T n i)) = pb h L (s i)) :=
  open Scheme.Modules ProjectiveSpace in by
    refine ⟨?_, ?_, ?_⟩
    · intro Y ψ
      constructor
      · exact (Scheme.Modules.invertible_pullback_tensor ψ).1 (O n) |>.2
      · intro y
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
          ((iSup_standardOpen (ULift.{u} (Fin (n + 1)))
            (Spec (CommRingCat.of (ULift.{u} ℤ)))).ge (Set.mem_univ (ψ y)))
        refine ⟨i.down, (nonvanishing_tensorPullback ψ (O n) (T n i.down) y).2 ?_⟩
        rw [projectiveSpace_standardCharts_part2]
        exact hi
    · intro Y L _ s hs
      let t : ULift.{u} (Fin (n + 1)) → Γ(L, ⊤) := fun i ↦ s i.down
      let U : ULift.{u} (Fin (n + 1)) → Y.Opens := fun i ↦ generatingLocus (t i)
      have hU : ⨆ i, U i = ⊤ := by
        apply eq_top_iff.mpr
        intro y _
        obtain ⟨i, hi⟩ := hs y
        exact TopologicalSpace.Opens.mem_iSup.mpr
          ⟨ULift.up i, (mem_nonvanishingLocus_iff_generatesAt L (s i) y).1 hi⟩
      have ht (i) : IsFreeGenerator
          (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (t i)) :=
        isFreeGenerator_generatingLocus (t i)
      obtain ⟨ψ, _, ε, hε, hεs⟩ := exists_hom_twistRestrict t U ht
        (specULiftZIsTerminal.from Y) hU
      let c := ((Classical.choose (exists_tensorPullbackAdjunction ψ)).leftAdjointUniq
        (pullbackPushforwardAdjunction ψ)).app (O n)
      let e : (tensorPullback ψ).obj (O n) ≅ L := c ≪≫ asIso ε
      have hes (i : Fin (n + 1)) : e.hom.app ⊤ (pb ψ (O n) (T n i)) = s i := by
        change ε.app ⊤ (c.hom.app ⊤ (pb ψ (O n) (T n i))) = _
        rw [tensorComparison_section]
        simpa only [Scheme.Hom.preimage_top, presheaf_map_id_apply] using hεs (ULift.up i)
      refine ⟨ψ, ⟨e, hes⟩, ?_⟩
      intro χ hχ
      obtain ⟨eχ, heχ⟩ := hχ
      let cχ := ((Classical.choose (exists_tensorPullbackAdjunction χ)).leftAdjointUniq
        (pullbackPushforwardAdjunction χ)).app (O n)
      let aχ : twistRestrict χ 1 ≅ L := cχ.symm ≪≫ eχ
      have hχs (i : ULift.{u} (Fin (n + 1))) :
          aχ.hom.app ⊤ (pullbackSection χ (twistOneSection _ _ i)) = t i := by
        rw [← tensorComparison_section χ (O n) (T n i.down)]
        change eχ.hom.app ⊤
          (cχ.inv.app ⊤ (cχ.hom.app ⊤ (pb χ (O n) (T n i.down)))) = _
        simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app,
          cχ.hom_inv_id, Hom.id_app, ConcreteCategory.id_apply] using heχ i.down
      apply projective_pair_injective t aχ (asIso ε) hχs
      · intro i
        simpa only [Scheme.Hom.preimage_top, presheaf_map_id_apply, asIso_hom] using hεs i
      · exact specULiftZIsTerminal.hom_ext _ _
    · intro Y Y' h ψ L s e he
      obtain ⟨c, hc⟩ := (Scheme.Modules.invertible_pullback_tensor ψ).2.2.2.1 Y' h (O n)
      refine ⟨c.symm ≪≫ (tensorPullback h).mapIso e, ?_⟩
      intro i
      have hci := hc ⊤ (T n i)
      have hcinv : c.inv.app ⊤ (pb (h ≫ ψ) (O n) (T n i)) =
          pb h ((tensorPullback ψ).obj (O n)) (pb ψ (O n) (T n i)) := by
        apply (ConcreteCategory.bijective_of_isIso (c.hom.app ⊤)).1
        simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app,
          c.inv_hom_id, Hom.id_app, ConcreteCategory.id_apply, Scheme.Hom.preimage_top]
          using hci.symm
      change ((tensorPullback h).map e.hom).app ⊤
        (c.inv.app ⊤ (pb (h ≫ ψ) (O n) (T n i))) = _
      rw [hcinv, tensorPullback_section_naturality, he]

end AlgebraicGeometry
