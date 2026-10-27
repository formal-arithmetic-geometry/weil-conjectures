/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.RationalPurityCoefficientModels
import all Sheaf.Paper.IntegralCompactSupportUniformRestriction
import Sheaf.Paper.IntegralCompletedLocalPerfectCriterion
import Sheaf.Paper.ExtensionZeroStratifiedPerfect
import Sheaf.Paper.CompletedConstructiblePreservation
import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr

/-! # Compact support on the lifted PBC integral lattices

This is the compact-support preservation step of the rational purity presentation.
The coefficient ring is the published lifted PBC ring, with its actual quotient tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] pbcPurityCompactAmbient

/-- The actual proper/open image preserves the lifted PBC lattice category.

Source: Bhatt--Scholze, Lemmas 6.7.2 and 6.7.7; blueprint
prop-pur-rational-purity-transitivity-summands, Step 1, and
lem-cbc-integral-compact-support-uniform-restriction, preservation clause.
(blueprint: lem-pur-lifted-compact-support-lattices).

Proof: a proper compactification over the Noetherian finite-dimensional target is
Noetherian and finite-dimensional. Pull back the target's inverse of l to it.
Use the stratified local-perfect criterion for the actual lifted valuation ring:
extension by zero extends each input stratum through the open immersion, and
adds the closed complement with zero perfect model. The open unit retains the
old local models, and restriction to the complement vanishes. Thus extension by
zero is constructible complete with a common reduction bound. Proper direct
image preserves constructible completeness with a common bound enlarged by the
finite geometric-fibre dimension bound. Its right adjunction commutes with the
reduction-limit comparison. The finite-quotient-normalized coefficient maps
identify these operations with the displayed proper/open image. Transport along
the valuation-ring ULift equivalence preserves the actual reductions, completion
unit and local models; it is not an identification of the two ring types by
reduction. This is the proof of the uniform-restriction theorem applied to the
lifted ring. The empty scheme and zero input use the zero local model. -/
theorem pbcPurityCompact_lattices (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (c : Compactification f)
    [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
      ((pbcPurityCompactAmbient l E c).obj K.obj) := by
  classical
  let δ := pbcIntegralDatum l E
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have hZdim := AlgebraicGeometry.finiteType_source_dimension_bound c.g dY.out
  have hXl : IsUnit (l : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using iX.out x
  have hYl : IsUnit (l : Γ(Y, ⊤)) := by
    apply Y.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    simpa only [map_natCast] using iY.out y
  have hZl : IsUnit (l : Γ(c.Z, ⊤)) := by
    simpa only [map_natCast] using hYl.map c.g.appTop.hom
  let J := (cbcDerivedOpenShriek δ c.i inferInstance).obj K.obj
  have hJ : PbcIsBoundedConstructibleComplete c.Z δ J := by
    apply (integralCompletedLocalPerfectCriterion c.Z l E hZdim hZl J).mpr
    have hK := (integralCompletedLocalPerfectCriterion X l E dX.out hXl K.obj).mp K.property
    have hcover : Set.range c.i ∪ Set.range c.i.closedComplement = Set.univ := by
      rw [Scheme.Hom.range_closedComplement, Set.union_compl_self]
    have hdisjoint : Disjoint (Set.range c.i) (Set.range c.i.closedComplement) := by
      rw [Scheme.Hom.range_closedComplement]
      exact disjoint_compl_right
    exact (cbc_extension_zero_stratified_perfect l E c.i c.i.closedComplement
      hcover hdisjoint K.obj hK).1
  have hAnn : (l : PbcIntegralRing l E ⧸ δ.ideal) = 0 := by
    have H := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
    have hgen := H.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hl : (l : Padic.coefficientExtensionIntegers l E) ∈
        Ideal.span {Padic.coefficientExtensionUniformizer l E} := by
      change Ideal.span {Padic.coefficientExtensionUniformizer l E} =
        Padic.coefficientExtensionMaximalIdeal l E at hgen
      rw [hgen]
      apply (H.2.1 _).2
      have h := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
      rw [map_natCast] at h
      change spectralNorm ℚ_[l] E (l : E) < 1
      rw [h]
      exact Padic.norm_p_lt_one
    change Ideal.Quotient.mk δ.ideal (l : PbcIntegralRing l E) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (l : PbcIntegralRing l E) ∈ Ideal.span {pbcUniformizer l E}
    let ε : Padic.coefficientExtensionIntegers l E ≃+* PbcIntegralRing l E :=
      ULift.ringEquiv.symm
    have hm : Ideal.map ε.toRingHom
        (Ideal.span {Padic.coefficientExtensionUniformizer l E}) =
          Ideal.span {pbcUniformizer l E} := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    have h := Ideal.mem_map_of_mem ε.toRingHom hl
    rw [hm, map_natCast] at h
    exact h
  obtain ⟨e, he⟩ := hZdim
  have hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback c.g y : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
    intro Ω _ _ y
    exact (AlgebraicGeometry.topologicalKrullDim_pullback_le c.g y).trans he
  let s : IsPullback (𝟙 c.Z) c.g c.g (𝟙 Y) := .of_horiz_isIso ⟨by simp⟩
  let sq : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y) :=
    { w := by simp
      isoPullback := s.isoPullback
      hom_fst := s.isoPullback_hom_fst
      hom_snd := s.isoPullback_hom_snd }
  have hp := (δ.constructible_preservation sq ⟨e, he⟩ dY.out ⟨e, he⟩ dY.out
    l (Fact.out : l.Prime).pos hAnn hZl hYl hZl hYl e hfib J hJ).1
  have := (pbcIntegralUniformComplete_isTriangulated l E Y dY.out iY.out).1
  apply ObjectProperty.prop_of_iso (PbcIsBoundedConstructibleComplete Y δ) _ hp
  change (δ.push c.g).obj J ≅ _
  unfold pbcPurityCompactAmbient PurCompactSupport.image
  dsimp only [Functor.comp_obj, pbcPurityCoefficients]
  rw [coefficientIso_eq c.g δ]
  exact (δ.push c.g).mapIso ((openExtensionIso c.i δ).app K.obj).symm

end AlgebraicGeometry.Scheme
