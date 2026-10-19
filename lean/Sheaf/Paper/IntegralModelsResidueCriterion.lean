/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.IntegralModelsDefinitions
import Sheaf.Paper.IntegralModelsCompleteReflection
import Sheaf.Paper.IntegralModelsResidueComparison
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin

/-! # Residue interpretation of Stacks constructibility

Source: blueprint main-20261015, sk-lem-integral-models, proof steps 4--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem residueFinite (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ) : Finite (completedResidue ℓ E π n) := by
  change Finite ((PadicAlgCl.integers ℓ E.1) ⧸ (Ideal.span {π}) ^ (n + 1))
  rw [hπ]
  infer_instance

private theorem residueDiscrete (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)) :
    DiscreteTopology (completedResidue ℓ E π 0) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  change DiscreteTopology ((PadicAlgCl.integers ℓ E.1) ⧸ (Ideal.span {π}) ^ (0 + 1))
  rw [zero_add, pow_one, hπ]
  apply QuotientAddGroup.discreteTopology
  have hs : (IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) :
      Set (PadicAlgCl.integers ℓ E.1)) =
      {x : PadicAlgCl.integers ℓ E.1 | ‖(x : E.1)‖₊ < 1} := by
    ext x
    exact Valuation.mem_maximalIdeal_iff E.1 (PadicAlgCl.valuationOfAlgebra ℓ E.1)
  change IsOpen (IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) :
    Set (PadicAlgCl.integers ℓ E.1))
  rw [hs]
  exact isOpen_lt (continuous_nnnorm.comp continuous_subtype_val) continuous_const


/-- Stacks constructibility of a restricted complex is exactly completeness and bounded
constructible etale origin of its first derived residue reduction.

Source: blueprint main-20261015, sk-lem-integral-models, proof steps 4--6; Stacks 03ET,
06YQ, 099I, 099L, and 09AL.
(blueprint: lem-sfb-embedded-integral-residue-criterion).

Proof: rewriting the uniformizer ideal as the maximal ideal proves finiteness of
all positive residue quotients. Its first quotient has discrete topology: the maximal
ideal is the open valuation unit ball, so apply discreteness of the quotient topology.
Unpack the Stacks predicate and use embeddedIntegral_complete_iff for its completeness
conjunct. The first-residue cohomology comparison identifies the remaining two conjuncts
with constructible cohomology and bounded cohomology of the specified intrinsic
realization. That realization is exact by integralModelIntrinsicRealization_exact, so
its right-derived functor is canonically isomorphic to its termwise derived functor.
Apply finiteRing_constructibleDerived_origin to the termwise image. In the forward
direction compose its essential-image isomorphism with the inverse of the canonical
derived-functor comparison, and insert the finite/discrete witnesses. Conversely discard
those witnesses and compose the essential-image isomorphism with that comparison.
Thus the functor in the original residue-origin definition is preserved. The input
complex may be unbounded; zero objects and empty schemes need no separate construction. -/
theorem embeddedIntegral_residue_criterion
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E))) :
    IntegralModelsEmbedded.stacksConstructible ℓ E π X
        ((IntegralModelsEmbedded.restriction ℓ E X).obj K) ↔
      IntegralModelsEmbedded.completedComplete ℓ E π X K ∧
        integralModelResidueEtaleOrigin X ℓ E π K := by
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  let : Finite (completedResidue ℓ E π 0) := residueFinite ℓ E π hπ 0
  let : DiscreteTopology (completedResidue ℓ E π 0) := residueDiscrete ℓ E π hπ
  let F := integralModelIntrinsicRealization.{u} X (completedResidue ℓ E π 0)
  have : PreservesFiniteLimits F :=
    (integralModelIntrinsicRealization_exact.{u} X (completedResidue ℓ E π 0)).1
  have : PreservesFiniteColimits F :=
    (integralModelIntrinsicRealization_exact.{u} X (completedResidue ℓ E π 0)).2
  let : Abelian.HasKInjectiveResolutions
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj (completedResidue ℓ E π 0)) X)) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  let K₁ := (integralModelFirstDerivedReduction.{u} X ℓ E π).obj K
  let R := (integralModelIntrinsicDerivedRealization.{u} X (completedResidue ℓ E π 0)).obj K₁
  let e : F.rightDerivedFunctor.obj K₁ ≅ R :=
    F.rightDerivedFunctorIsoMapDerivedCategory.app K₁
  have hc := embeddedIntegral_residue_comparison ℓ E π hπ X K
  have ho := (Scheme.finiteRing_constructibleDerived_origin X
    (ULift.{u, 0} (completedResidue ℓ E π 0))).2.2.1 R
  change (_ ∧ _) ↔ _
  apply and_congr (embeddedIntegral_complete_iff ℓ E π hπ X K)
  refine hc.trans (ho.symm.trans ?_)
  constructor
  · rintro ⟨M, ⟨i⟩⟩
    exact ⟨inferInstance, inferInstance, M, ⟨i ≪≫ e.symm⟩⟩
  · rintro ⟨_, _, M, ⟨i⟩⟩
    exact ⟨M, ⟨i ≪≫ e⟩⟩

end AlgebraicGeometry.ProEtale
