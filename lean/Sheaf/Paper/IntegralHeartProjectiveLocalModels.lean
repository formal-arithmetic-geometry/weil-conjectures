/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.IntegralHeartLocalModelData
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.Paper.IntegralHeartCompletedComparison
import all Sheaf.Paper.IntegralCohomologicalAdicCriterion
import all Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-! # Projective local models for integral scalar realization

Source: the current blueprint, integral-heart-local-model, clause (1).
(blueprint: lem-sfb-integral-heart-projective-local-models)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private instance integralHeart_domain
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    IsDomain (integralHeartScalars.{u} ℓ E) :=
  MulEquiv.isDomain (SmallAdicCompletion.Coefficients.integers ℓ E)
    ULift.ringEquiv.toMulEquiv

-- The arithmetic argument is universe-independent: only its outer ULift changes.
private theorem integralHeart_arithmetic
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    let I : Ideal (integralHeartScalars.{u} ℓ E) :=
      Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer ℓ
        (SmallAdicCompletion.Coefficients.field ℓ E))}
    IsDiscreteValuationRing (integralHeartScalars.{u} ℓ E) ∧
      IsAdicComplete I (integralHeartScalars.{u} ℓ E) ∧
      I.IsMaximal ∧ ∀ J : Ideal (integralHeartScalars.{u} ℓ E), J.IsMaximal → J = I := by
  let L := SmallAdicCompletion.Coefficients.field ℓ E
  let O := SmallAdicCompletion.Coefficients.integers ℓ E
  let R := integralHeartScalars.{u} ℓ E
  let I : Ideal R := Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer ℓ L)}
  let J : Ideal O := Ideal.span {Padic.coefficientExtensionUniformizer ℓ L}
  let e : O ≃+* R := ULift.ringEquiv.symm
  have h := (Padic.extension_integers_dvr ℓ L (Padic.coefficientExtensionAbsoluteValue ℓ L)
    (spectralNorm_extends (K := Padic ℓ) (L := L))).choose_spec.choose_spec
  let : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
  let : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hJ : J = Padic.coefficientExtensionMaximalIdeal ℓ L :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hI : J.map e = I := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hc : IsAdicComplete J O := hJ.symm ▸ Padic.coefficientIntegers_complete ℓ L
  have hcR : IsAdicComplete I R :=
    hI ▸ (IsAdicComplete.congr_ringEquiv J e).mpr hc
  have hm : I.IsMaximal := by
    rw [← hI]
    have hm : (Padic.coefficientExtensionMaximalIdeal ℓ L).IsMaximal := h.2.2.2.2.1
    rw [← hJ] at hm
    exact hm.map_bijective e e.bijective
  exact ⟨inferInstance, hcR, hm, fun Q hQ ↦
    (IsLocalRing.eq_maximalIdeal hQ).trans (IsLocalRing.eq_maximalIdeal hm).symm⟩

-- The forward cohomological criterion uses only a complete local DVR, not its field universe.
private theorem completedCohomology_perfect (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (Scheme.proEtaleRingModules X (Scheme.adicLisseCompletedRing X I)))
    (hb : DerivedCategory.TStructure.t.bounded K)
    (hcoh : ∀ q : ℤ, Scheme.IsCompletedConstantStratified X I
      ((DerivedCategory.homologyFunctor _ q).obj K)) : Scheme.IsSfbStratifiedPerfect X I K := by
  obtain ⟨hequiv, _, hzero, hiso, hshift, htriangle⟩ :=
    Scheme.adic_stratified_perfect X A I hI
  let P : ObjectProperty (Scheme.proEtaleRingModules X (Scheme.adicLisseCompletedRing X I)) :=
    Scheme.IsCompletedConstantStratified X I
  let Q : ObjectProperty (DerivedCategory
      (Scheme.proEtaleRingModules X (Scheme.adicLisseCompletedRing X I))) :=
    Scheme.IsSfbAdicConstructible X I
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ Scheme.completedStratified_of_iso e h⟩
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hiso _ _ ⟨e⟩ h⟩
  apply (hequiv K).mp
  apply DerivedCategory.prop_of_bounded_of_degreewise Q
    (fun L hL ↦ hiso _ L ⟨(isZero_zero _).isoZero ≪≫ hL.isoZero.symm⟩ hzero)
    (fun T hT h₁ h₃ ↦ (htriangle T hT).2.2 ⟨h₃, h₁⟩) (fun _ ↦ P) ?_ K hb hcoh
  intro q M hM
  have h₀ : Q ((DerivedCategory.singleFunctor _ 0).obj M) :=
    (hequiv _).mpr (Scheme.perfect_of_completedStratified X I M hM)
  exact hiso _ _
    ⟨((DerivedCategory.singleFunctors _).shiftIso (-q) q 0 (by omega)).app M⟩
    (hshift _ (-q) h₀)

/-- Bounded constructible integral complexes have bounded finite projective scalar
models on one finite constructible stratification and pro-etale covers of its strata.
This assertion only supplies the complex models, without a freeness assertion or a
comparison for their cohomology.

Source: Bhatt--Scholze, Proposition 6.6.11, and Proposition 6.8.11(3); the current
blueprint integral-heart-local-model, clause (1), before the projective-to-free step.
(blueprint: lem-sfb-integral-heart-projective-local-models)

Proof: pass to the canonical small presentation of E. Its valuation ring is a
complete local Noetherian DVR. Identify its continuous coefficient sheaf with the
inverse limit of the constant positive uniformizer quotients, projection by
projection, and use the section-action equivalence to read K as a complex of
modules over this ring sheaf. Finite constant presentations correspond under this
equivalence, and its exactness identifies cohomology; hence hK is the left side of
the integral cohomological adic criterion. That criterion gives local derived
completeness and a bounded constructible etale residue model of finite Tor
amplitude. Apply the forward direction of adic_stratified_perfect. Its bounded
finite projective scalar complexes live on the resulting constructible strata.
Refine the covering sieves in that statement to pro-etale covering families. The
slice-site equivalence identifies restriction to a member of each family with
inverse image to its scheme. Transport the model isomorphisms back through the
section-action and coefficient equivalences. The scalar comparison is the
canonical map sending a scalar to its constant continuous function; uniqueness
of extension of scalars identifies this composite with integralHeartRealization.
All these comparisons are exact equivalences or canonical scalar extensions, so
neither the original object K nor its local representative is completed again.
The same bounds and finite projective terms survive these identifications. -/
theorem integralHeart_projective_local_models
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (hK : constantModelBoundedConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X K) :
    ∃ s : Scheme.FiniteLocallyClosedStratification X,
      (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
      ∀ a : Fin s.n, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
        ∀ i : 𝒰.I₀,
          ∃ (P : CochainComplex (ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) ℤ)
            (b c : ℤ),
            P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
            (∀ q : ℤ, Module.Projective (integralHeartScalars.{u} ℓ E) (P.X q) ∧
              Module.Finite (integralHeartScalars.{u} ℓ E) (P.X q)) ∧
            Nonempty (((CondensedRing.upperStar
                (SmallAdicCompletion.Coefficients.integerRing ℓ E)
                (𝒰.f i ≫ s.immersion a)).mapDerivedCategory).obj K ≅
              DerivedCategory.Q.obj
                (((integralHeartRealization.{u} ℓ E (𝒰.X i)).mapHomologicalComplex
                  (.up ℤ)).obj P)) := by
  let I : Ideal (integralHeartScalars.{u} ℓ E) :=
    Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer ℓ
      (SmallAdicCompletion.Coefficients.field ℓ E))}
  obtain ⟨hdvr, hcomplete, hmax⟩ := integralHeart_arithmetic.{u} ℓ E
  let : IsDiscreteValuationRing (integralHeartScalars.{u} ℓ E) := hdvr
  let : IsAdicComplete I (integralHeartScalars.{u} ℓ E) := hcomplete
  obtain ⟨F, hconstruct, hlocal⟩ := integralHeart_completed_comparison.{u} ℓ E X
  let : F.functor.Additive := Functor.additive_of_preserves_binary_products _
  let L := F.functor.mapDerivedCategory.obj K
  have hcoh (q : ℤ) : Scheme.IsCompletedConstantStratified X I
      ((DerivedCategory.homologyFunctor _ q).obj L) := by
    exact Scheme.completedStratified_of_iso
      ((F.functor.mapDerivedCategoryHomologyFunctorIso q).app K)
      ((hconstruct _).mp (hK.2 q))
  obtain ⟨s, hs, hm⟩ := completedCohomology_perfect X _ I hmax L
    (F.functor.bounded_mapDerivedCategory_obj hK.1) hcoh
  refine ⟨{
    n := s.n
    stratum := s.stratum
    isLocallyClosed_stratum := s.isLocallyClosed_stratum
    iUnion_stratum_eq_univ := s.iUnion_stratum_eq_univ
    pairwise_disjoint_stratum := s.pairwise_disjoint_stratum
    domain := s.domain
    immersion := s.immersion
    isImmersion := s.isImmersion
    range_immersion := s.range_immersion }, hs, ?_⟩
  intro a
  obtain ⟨V, hV, hv⟩ := hm a
  let t := (Scheme.ProEt.isTerminalMkId (s.domain a)).uniqueUpToIso
    (terminalIsTerminal : IsTerminal (⊤_ (s.domain a).ProEt))
  obtain ⟨T, hT, hTV⟩ := Scheme.ProEt.mem_topology_iff.mp
    ((Scheme.ProEt.topology (s.domain a)).pullback_stable t.hom hV)
  obtain ⟨idx, Z, f, rfl⟩ := T.exists_eq_ofArrows
  let W : PreZeroHypercover (s.domain a) :=
    { I₀ := idx
      X := fun i ↦ (Z i).left
      f := fun i ↦ (Z i).hom }
  have hW : W.presieve₀ ∈ Scheme.proetalePrecoverage (s.domain a) := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hT
    have hw (i : idx) : (f i).left = (Z i).hom := by
      exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w (f i))
    change Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      Scheme.proetalePrecoverage (s.domain a) at hT
    simpa only [hw] using hT
  let : Precoverage.Small.{u} Scheme.proetalePrecoverage := by
    change Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale)
    infer_instance
  let 𝒱 : Scheme.Cover Scheme.proetalePrecoverage (s.domain a) := ⟨W, hW⟩
  let 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a) :=
    Precoverage.ZeroHypercover.restrictIndexOfSmall.{u} 𝒱
  refine ⟨𝒰, fun i ↦ ?_⟩
  let j := Precoverage.ZeroHypercover.Small.restrictFun.{u} 𝒱 i
  obtain ⟨P, b, c, _, hb, hc, hP, e⟩ := hv (Z j) (f j ≫ t.hom) (hTV _ _ ⟨j⟩)
  let : IsImmersion (s.immersion a) := s.isImmersion a
  refine ⟨P, b, c, hb, hc, hP, ?_⟩
  have he := (hlocal (s.domain a) (s.immersion a) (Z j) K P).mp e
  simpa only [𝒰, Precoverage.ZeroHypercover.restrictIndexOfSmall,
    PreZeroHypercover.restrictIndex, Function.comp_apply, j, 𝒱, W] using he

end AlgebraicGeometry.ProEtale
