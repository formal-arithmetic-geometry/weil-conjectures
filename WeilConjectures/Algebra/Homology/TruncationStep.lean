/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# One step of the canonical truncation of a cochain complex

Let `K` be a cochain complex in an abelian category and `q₀ + 1 = q`. The canonical
truncations `τ_{≤ q₀} K ⊆ τ_{≤ q} K` (`CochainComplex.truncLE`) differ by the cohomology of `K`
in degree `q`. We construct:

* the inclusion `i_q : τ_{≤ q₀} K ⟶ τ_{≤ q} K` (`CochainComplex.truncLEMapOfLE`), natural in `K`;
* the projection `j_q : τ_{≤ q} K ⟶ H^q(K)[-q]` (`CochainComplex.truncLEToSingle`), which in
  degree `q` is the projection `Ker d^q ⟶ H^q(K)`, natural in `K`;
* the short exact sequence `0 ⟶ τ_{≤ q₀} K ⟶ τ_{≤ q} K ⟶ M_q(K) ⟶ 0` with `M_q(K)` the
  cokernel of `i_q` (`CochainComplex.truncLEStep`, `CochainComplex.truncLEStep_shortExact`);
* the factorisation `j_q = j̄_q ∘ p_q` through a quasi-isomorphism
  `j̄_q : M_q(K) ⟶ H^q(K)[-q]` (`CochainComplex.truncLEStepToSingle`,
  `CochainComplex.quasiIso_truncLEStepToSingle`).

This is blueprint `lem-weil-pbc-truncation-step-ses` (Stacks, Remark 08J5). We also record the
cohomology of the canonical truncation, blueprint `lem-weil-pbc-truncation-cohomology`
(`CochainComplex.isIso_homologyMap_ιTruncLE`, `CochainComplex.isZero_homology_truncLE`).

The facts that cochain complexes form an abelian category in which short exactness is
degreewise (blueprint `lem-weil-pbc-cochain-complexes-degreewise-exact`,
`HomologicalComplex.shortExact_iff_degreewise_shortExact`) and that the coimage maps
monomorphically to the target (blueprint `lem-weil-pbc-coimage-mono`,
`CategoryTheory.Abelian.instMonoFactorThruCoimage`) are in Mathlib.
-/

@[expose] public section

open CategoryTheory Category Limits HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

section Cohomology

variable (K : CochainComplex C ℤ)

/-- This is blueprint `lem-weil-pbc-truncation-cohomology`, first part: the inclusion
`τ_{≤ n} K ⟶ K` induces isomorphisms in cohomology in degrees `i ≤ n` (Mathlib
`CochainComplex.quasiIsoAt_ιTruncLE`). -/
lemma isIso_homologyMap_ιTruncLE (n i : ℤ) (hi : i ≤ n) :
    IsIso (homologyMap (K.ιTruncLE n) i) :=
  (quasiIsoAt_iff_isIso_homologyMap _ _).mp (K.quasiIsoAt_ιTruncLE n i hi)

/-- This is blueprint `lem-weil-pbc-truncation-cohomology`, second part: the canonical
truncation `τ_{≤ n} K` has no cohomology in degrees `i > n`. -/
lemma isZero_homology_truncLE (n i : ℤ) (hi : n < i) : IsZero ((K.truncLE n).homology i) :=
  (K.truncLE n).isZero_of_isLE n i hi

end Cohomology

section Inclusion

variable (K L M : CochainComplex C ℤ) (φ : K ⟶ L) (ψ : L ⟶ M)

instance (n : ℤ) : Mono (K.ιTruncLE n) := by
  dsimp only [CochainComplex.ιTruncLE]
  infer_instance

/-- For `a ≤ b`, the inclusion `τ_{≤ a} K ⟶ τ_{≤ b} K` of canonical truncations. -/
noncomputable def truncLEMapOfLE (a b : ℤ) (h : a ≤ b) : K.truncLE a ⟶ K.truncLE b :=
  have : (K.truncLE a).IsStrictlyLE b := (K.truncLE a).isStrictlyLE_of_le a b h
  inv ((K.truncLE a).ιTruncLE b) ≫ truncLEMap (K.ιTruncLE a) b

@[reassoc (attr := simp)]
lemma truncLEMapOfLE_ιTruncLE (a b : ℤ) (h : a ≤ b) :
    K.truncLEMapOfLE a b h ≫ K.ιTruncLE b = K.ιTruncLE a := by
  have : (K.truncLE a).IsStrictlyLE b := (K.truncLE a).isStrictlyLE_of_le a b h
  simp only [truncLEMapOfLE, assoc]
  rw [CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

instance (a b : ℤ) (h : a ≤ b) : Mono (K.truncLEMapOfLE a b h) :=
  mono_of_mono_fac (K.truncLEMapOfLE_ιTruncLE a b h)

variable {K L} in
@[reassoc (attr := simp)]
lemma truncLEMapOfLE_naturality (a b : ℤ) (h : a ≤ b) :
    truncLEMap φ a ≫ L.truncLEMapOfLE a b h = K.truncLEMapOfLE a b h ≫ truncLEMap φ b := by
  rw [← cancel_mono (L.ιTruncLE b), assoc, truncLEMapOfLE_ιTruncLE,
    CochainComplex.ιTruncLE_naturality, assoc, CochainComplex.ιTruncLE_naturality,
    truncLEMapOfLE_ιTruncLE_assoc]

end Inclusion

section Projection

variable (K L M : CochainComplex C ℤ) (φ : K ⟶ L) (ψ : L ⟶ M) (q : ℤ)

instance : IsIso ((K.truncLE q).iCycles q) :=
  (K.truncLE q).isIso_iCycles q (q + 1) (by simp)
    (((K.truncLE q).isZero_of_isStrictlyLE q (q + 1) (by lia)).eq_of_tgt _ _)

/-- The component in degree `q` of `CochainComplex.truncLEToSingle`: the projection
`(τ_{≤ q} K)^q = Ker d^q_K ⟶ H^q(K)`. -/
noncomputable def truncLEToHomology : (K.truncLE q).X q ⟶ K.homology q :=
  inv ((K.truncLE q).iCycles q) ≫ (K.truncLE q).homologyπ q ≫ homologyMap (K.ιTruncLE q) q

@[reassoc (attr := simp)]
lemma iCycles_truncLEToHomology :
    (K.truncLE q).iCycles q ≫ K.truncLEToHomology q =
      (K.truncLE q).homologyπ q ≫ homologyMap (K.ιTruncLE q) q := by
  simp [truncLEToHomology]

@[reassoc (attr := simp)]
lemma d_truncLEToHomology (i : ℤ) : (K.truncLE q).d i q ≫ K.truncLEToHomology q = 0 := by
  rw [← (K.truncLE q).toCycles_i i q, assoc, iCycles_truncLEToHomology,
    toCycles_comp_homologyπ_assoc, zero_comp]

/-- The projection `j_q : τ_{≤ q} K ⟶ H^q(K)[-q]` onto the cohomology of `K` in degree `q`,
placed in degree `q` (blueprint `lem-weil-pbc-truncation-step-ses` (b)). -/
noncomputable def truncLEToSingle :
    K.truncLE q ⟶ (single C (ComplexShape.up ℤ) q).obj (K.homology q) :=
  mkHomToSingle (K.truncLEToHomology q) (fun i _ ↦ K.d_truncLEToHomology q i)

@[simp]
lemma truncLEToSingle_f :
    (K.truncLEToSingle q).f q = K.truncLEToHomology q ≫ (singleObjXSelf _ q _).inv :=
  mkHomToSingle_f _ _

variable {K L} in
@[reassoc (attr := simp)]
lemma truncLEToHomology_naturality :
    (truncLEMap φ q).f q ≫ L.truncLEToHomology q =
      K.truncLEToHomology q ≫ homologyMap φ q := by
  rw [← cancel_epi ((K.truncLE q).iCycles q), ← cyclesMap_i_assoc, iCycles_truncLEToHomology,
    iCycles_truncLEToHomology_assoc, ← homologyπ_naturality_assoc, ← homologyMap_comp,
    ← homologyMap_comp, CochainComplex.ιTruncLE_naturality]

variable {K L} in
@[reassoc (attr := simp)]
lemma truncLEToSingle_naturality :
    truncLEMap φ q ≫ L.truncLEToSingle q =
      K.truncLEToSingle q ≫ (single C (ComplexShape.up ℤ) q).map (homologyMap φ q) := by
  apply to_single_hom_ext
  simp [single_map_f_self, truncLEToHomology_naturality_assoc]

/-- The projection `j_q` induces on `H^q` the map induced by the inclusion `τ_{≤ q} K ⟶ K`,
an isomorphism. -/
@[reassoc]
lemma homologyMap_truncLEToSingle :
    homologyMap (K.truncLEToSingle q) q ≫ (singleObjHomologySelfIso _ q _).hom =
      homologyMap (K.ιTruncLE q) q := by
  rw [← cancel_epi ((K.truncLE q).homologyπ q), homologyπ_naturality_assoc,
    homologyπ_singleObjHomologySelfIso_hom, singleObjCyclesSelfIso_hom, cyclesMap_i_assoc,
    truncLEToSingle_f, assoc, Iso.inv_hom_id, comp_id, iCycles_truncLEToHomology]

instance : IsIso (homologyMap (K.truncLEToSingle q) q) := by
  have := K.isIso_homologyMap_ιTruncLE q q le_rfl
  exact IsIso.of_isIso_fac_right (K.homologyMap_truncLEToSingle q)

end Projection

section Step

variable (K L : CochainComplex C ℤ) (q₀ q : ℤ) (hq : q₀ + 1 = q)

include hq in
/-- The inclusion `i_q : τ_{≤ q₀} K ⟶ τ_{≤ q} K` followed by the projection
`j_q : τ_{≤ q} K ⟶ H^q(K)[-q]` is zero. -/
@[reassoc (attr := simp)]
lemma truncLEMapOfLE_truncLEToSingle :
    K.truncLEMapOfLE q₀ q (by lia) ≫ K.truncLEToSingle q = 0 := by
  apply to_single_hom_ext
  rw [comp_f]
  exact ((K.truncLE q₀).isZero_of_isStrictlyLE q₀ q (by lia)).eq_of_src _ _

/-- The short exact sequence `0 ⟶ τ_{≤ q₀} K ⟶ τ_{≤ q} K ⟶ M_q(K) ⟶ 0` of blueprint
`lem-weil-pbc-truncation-step-ses` (a), where `M_q(K)` is the cokernel of the inclusion
`i_q`. -/
@[simps!]
noncomputable abbrev truncLEStep : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (K.truncLEMapOfLE q₀ q (by lia)) (cokernel.π _) (cokernel.condition _)

/-- This is blueprint `lem-weil-pbc-truncation-step-ses` (a): the sequence
`0 ⟶ τ_{≤ q₀} K ⟶ τ_{≤ q} K ⟶ M_q(K) ⟶ 0` is short exact. -/
lemma truncLEStep_shortExact : (K.truncLEStep q₀ q hq).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/-- The morphism `j̄_q : M_q(K) ⟶ H^q(K)[-q]` induced by `j_q` on the cokernel of `i_q`
(blueprint `lem-weil-pbc-truncation-step-ses` (b)). -/
noncomputable def truncLEStepToSingle :
    (K.truncLEStep q₀ q hq).X₃ ⟶ (single C (ComplexShape.up ℤ) q).obj (K.homology q) :=
  cokernel.desc _ (K.truncLEToSingle q) (K.truncLEMapOfLE_truncLEToSingle q₀ q hq)

@[reassoc (attr := simp)]
lemma truncLEStep_g_truncLEStepToSingle :
    (K.truncLEStep q₀ q hq).g ≫ K.truncLEStepToSingle q₀ q hq = K.truncLEToSingle q :=
  cokernel.π_desc _ _ _

include hq in
lemma isIso_homologyMap_truncLEMapOfLE (r : ℤ) (hr : r ≤ q₀) :
    IsIso (homologyMap (K.truncLEStep q₀ q hq).f r) := by
  have := K.isIso_homologyMap_ιTruncLE q₀ r hr
  have := K.isIso_homologyMap_ιTruncLE q r (by lia)
  have h : homologyMap (K.truncLEStep q₀ q hq).f r ≫ homologyMap (K.ιTruncLE q) r =
      homologyMap (K.ιTruncLE q₀) r := by
    rw [← homologyMap_comp, truncLEMapOfLE_ιTruncLE]
  exact IsIso.of_isIso_fac_right h

lemma isZero_homology_truncLEStep_X₃ (r : ℤ) (hr : r ≠ q) :
    IsZero ((K.truncLEStep q₀ q hq).X₃.homology r) := by
  have hS := K.truncLEStep_shortExact q₀ q hq
  obtain hr | hr := lt_or_gt_of_ne hr
  · -- `r ≤ q₀`: the connecting map and `H^r(p_q)` both vanish
    have := K.isIso_homologyMap_truncLEMapOfLE q₀ q hq r (by lia)
    have h₁ : homologyMap (K.truncLEStep q₀ q hq).g r = 0 :=
      (hS.homology_exact₂ r).epi_f_iff.1 inferInstance
    have : Mono (homologyMap (K.truncLEStep q₀ q hq).f (r + 1)) := by
      by_cases h : r + 1 ≤ q₀
      · have := K.isIso_homologyMap_truncLEMapOfLE q₀ q hq (r + 1) h
        infer_instance
      · exact (K.isZero_homology_truncLE q₀ (r + 1) (by lia)).mono _
    have h₂ : hS.δ r (r + 1) rfl = 0 := (hS.homology_exact₁ r (r + 1) rfl).mono_g_iff.1 this
    exact (hS.homology_exact₃ r (r + 1) rfl).isZero_of_both_zeros h₁ h₂
  · -- `r > q`: both neighbours vanish
    exact (hS.homology_exact₃ r (r + 1) rfl).isZero_of_both_zeros
      ((K.isZero_homology_truncLE q r (by lia)).eq_of_src _ _)
      ((K.isZero_homology_truncLE q₀ (r + 1) (by lia)).eq_of_tgt _ _)

/-- This is blueprint `lem-weil-pbc-truncation-step-ses` (b): the morphism
`j̄_q : M_q(K) ⟶ H^q(K)[-q]` is a quasi-isomorphism. -/
instance quasiIso_truncLEStepToSingle : QuasiIso (K.truncLEStepToSingle q₀ q hq) where
  quasiIsoAt r := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    by_cases hr : r = q
    · subst hr
      have hS := K.truncLEStep_shortExact q₀ r hq
      have : Mono (homologyMap (K.truncLEStep q₀ r hq).g r) :=
        (hS.homology_exact₂ r).mono_g_iff.2
          ((K.isZero_homology_truncLE q₀ r (by lia)).eq_of_src _ _)
      have : Epi (homologyMap (K.truncLEStep q₀ r hq).g r) :=
        (hS.homology_exact₃ r (r + 1) rfl).epi_f_iff.2
          ((K.isZero_homology_truncLE q₀ (r + 1) (by lia)).eq_of_tgt _ _)
      have : IsIso (homologyMap (K.truncLEStep q₀ r hq).g r) := isIso_of_mono_of_epi _
      have h : homologyMap (K.truncLEStep q₀ r hq).g r ≫
          homologyMap (K.truncLEStepToSingle q₀ r hq) r =
            homologyMap (K.truncLEToSingle r) r := by
        rw [← homologyMap_comp, truncLEStep_g_truncLEStepToSingle]
      exact IsIso.of_isIso_fac_left h
    · exact ⟨0, (K.isZero_homology_truncLEStep_X₃ q₀ q hq r hr).eq_of_src _ _,
        (isZero_single_obj_homology _ _ _ _ hr).eq_of_src _ _⟩

variable {K L}

/-- The morphism `(τ_{≤ q₀} φ, τ_{≤ q} φ, M_q(φ))` of short exact sequences induced by a
morphism of complexes `φ : K ⟶ L`. -/
noncomputable def truncLEStepMap (φ : K ⟶ L) :
    K.truncLEStep q₀ q hq ⟶ L.truncLEStep q₀ q hq where
  τ₁ := truncLEMap φ q₀
  τ₂ := truncLEMap φ q
  τ₃ := cokernel.map _ _ (truncLEMap φ q₀) (truncLEMap φ q)
    (truncLEMapOfLE_naturality φ q₀ q (by lia)).symm
  comm₁₂ := truncLEMapOfLE_naturality φ q₀ q (by lia)
  comm₂₃ := by simp

@[simp]
lemma truncLEStepMap_τ₁ (φ : K ⟶ L) : (truncLEStepMap q₀ q hq φ).τ₁ = truncLEMap φ q₀ := rfl

@[simp]
lemma truncLEStepMap_τ₂ (φ : K ⟶ L) : (truncLEStepMap q₀ q hq φ).τ₂ = truncLEMap φ q := rfl

/-- This is blueprint `lem-weil-pbc-truncation-step-ses` (c): the quasi-isomorphism `j̄_q` is
natural in `K`. -/
@[reassoc (attr := simp)]
lemma truncLEStepToSingle_naturality (φ : K ⟶ L) :
    (truncLEStepMap q₀ q hq φ).τ₃ ≫ L.truncLEStepToSingle q₀ q hq =
      K.truncLEStepToSingle q₀ q hq ≫
        (single C (ComplexShape.up ℤ) q).map (homologyMap φ q) := by
  rw [← cancel_epi (K.truncLEStep q₀ q hq).g]
  have := (truncLEMap φ q ≫= L.truncLEStep_g_truncLEStepToSingle q₀ q hq).trans
    (truncLEToSingle_naturality φ q)
  simpa [truncLEStepMap] using this

end Step

end CochainComplex
