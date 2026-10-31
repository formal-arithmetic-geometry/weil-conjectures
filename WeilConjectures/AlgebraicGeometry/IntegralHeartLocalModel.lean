/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralHeartLocalModelData
public import WeilConjectures.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
import WeilConjectures.AlgebraicGeometry.IntegralHeartRealizationExact
import WeilConjectures.AlgebraicGeometry.IntegralHeartScalarComplexCoordinates
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransportSupplement
import all WeilConjectures.AlgebraicGeometry.QcqsIntegralFiniteModelCompleteness
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# Integral constructible local models

Source: the current blueprint, integral-heart-local-model, clauses (1)--(3).
Stacks Project, Tags 099I, 09C7, 09C4, 0990, 099Q and 099Y.
(blueprint: det-lem-int-integral-heart-local-model)

The integral criterion supplies bounded finite free condensed complexes. Scalar
coordinates and the comparison of the two point realizations identify these with
ordinary scalar complexes, on the same charts used for the cohomology comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem localModel_cohomology_truncations
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (hK : constantModelBoundedConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X K) :
    (∀ q : ℤ,
      SmallAdicCompletion.IsDerivedComplete ℓ E X (integralHeartCohomology ℓ E X K q) ∧
      constantModelBoundedConstructible
        (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
        (integralHeartCohomology ℓ E X K q)) ∧
    (∀ q : ℤ,
      constantModelBoundedConstructible
        (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
        ((DerivedCategory.TStructure.t.truncLE q).obj K) ∧
      constantModelBoundedConstructible
        (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
        ((DerivedCategory.TStructure.t.truncGE q).obj K)) := by
  let Λ := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  let P : ObjectProperty _ := IsConstantModelConstructible Λ X
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ constantModelConstructible_transport Λ e h⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
  have : P.ContainsZero :=
    ⟨_, DerivedCategory.isZero_of_isLE K b (b + 1) (by omega), hK.2 (b + 1)⟩
  constructor
  · intro q
    constructor
    · exact complete_sheaf ℓ (SmallAdicCompletion.Coefficients.field.{u} ℓ E) X
        ((DerivedCategory.homologyFunctor _ q).obj K) (hK.2 q)
    · refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
      intro r
      by_cases hr : r = 0
      · subst r
        exact P.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
          ((DerivedCategory.homologyFunctor _ q).obj K)).symm (hK.2 q)
      · apply P.prop_of_isZero
        rcases lt_or_gt_of_ne hr with hr | hr
        · exact DerivedCategory.isZero_of_isGE _ 0 r hr
        · exact DerivedCategory.isZero_of_isLE _ 0 r hr
  · intro q
    exact ⟨⟨⟨⟨a, inferInstance⟩, ⟨q, inferInstance⟩⟩,
        DerivedCategory.homologyProperty_truncLE hK.2 q⟩,
      ⟨⟨⟨q, inferInstance⟩, ⟨b, inferInstance⟩⟩,
        DerivedCategory.homologyProperty_truncGE hK.2 q⟩⟩

private theorem scalarHomology_finite
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (P : CochainComplex (ModuleCat A) ℤ) (q : ℤ)
    [Module.Finite A (P.X q)] : Module.Finite A (P.homology q) := by
  have : Module.Finite A (P.cycles q) :=
    Module.Finite.of_injective (P.iCycles q).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (P.homologyπ q).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

private theorem exactModel_homology
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (F : A ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory B) (P : CochainComplex A ℤ)
    (eK : G.mapDerivedCategory.obj K ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) (q : ℤ) :
    Nonempty (G.obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      F.obj (P.homology q)) := by
  exact ⟨(G.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso eK ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
    (F.mapHomologicalComplexHomologyIso (.up ℤ) q).app P⟩

private theorem scalarModel_homology
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (P : CochainComplex (ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) ℤ)
    (heK : Nonempty (((CondensedRing.upperStar
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) f).mapDerivedCategory).obj K ≅
        DerivedCategory.Q.obj
          (((integralHeartRealization.{u} ℓ E Y).mapHomologicalComplex (.up ℤ)).obj P)))
    (q : ℤ) :
    Nonempty ((CondensedRing.upperStar
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) f).obj
        ((DerivedCategory.homologyFunctor _ q).obj K) ≅
          (integralHeartRealization.{u} ℓ E Y).obj (P.homology q)) := by
  have : PreservesFiniteLimits (integralHeartRealization.{u} ℓ E Y) :=
    (integralHeartRealization_exact_free ℓ E Y).1
  have : PreservesFiniteColimits (integralHeartRealization.{u} ℓ E Y) :=
    (integralHeartRealization_exact_free ℓ E Y).2.1
  obtain ⟨eK⟩ := heK
  exact exactModel_homology
    (CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E) f)
    (integralHeartRealization.{u} ℓ E Y) K P eK q

private theorem localModel_realization_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u})
    [Functor.PreservesZeroMorphisms ((upperStarFromPoint X).mapMod
      (SmallAdicCompletion.Coefficients.integerRing ℓ E))]
    [((upperStarFromPoint X).mapMod
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).Additive]
    (C : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (SmallAdicCompletion.Coefficients.integerRing ℓ E)) ℤ)
    (P : CochainComplex (ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) ℤ)
    (eP : C ≅ ((integralHeartContinuousRealization.{u} ℓ E).mapHomologicalComplex
      (.up ℤ)).obj P)
    (e : integralHeartContinuousRealization.{u} ℓ E ≅
      integralHeartPointRealization.{u} ℓ E) :
    Nonempty (((((upperStarFromPoint X).mapMod
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).mapHomologicalComplex
        (.up ℤ)).obj C) ≅
      (((integralHeartRealization.{u} ℓ E X).mapHomologicalComplex
        (.up ℤ)).obj P)) := by
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
      AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
    dsimp [pointUpperStar, Functor.sheafPullbackConstruction.sheafPullback]
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  let G := (upperStarFromPoint X).mapMod
    (SmallAdicCompletion.Coefficients.integerRing ℓ E)
  have : PreservesFiniteLimits G := by
    dsimp [G]
    infer_instance
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  let F := integralHeartRealization.{u} ℓ E X
  let ePoint : C ≅ ((integralHeartPointRealization.{u} ℓ E).mapHomologicalComplex
      (.up ℤ)).obj P := eP ≪≫ (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  exact ⟨(G.mapHomologicalComplex (.up ℤ)).mapIso ePoint ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (integralHeartPointRealization.{u} ℓ E ⋙ G)) (.up ℤ)).app P)⟩

private theorem localModel_chart
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    [IsNoetherianRing (integralHeartScalars.{u} ℓ E)]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (C : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (SmallAdicCompletion.Coefficients.integerRing ℓ E)) ℤ)
    (b c : ℤ) (hb : C.IsStrictlyGE b) (hc : C.IsStrictlyLE c)
    (hC : ∀ q, Mod.IsFree (SmallAdicCompletion.Coefficients.integerRing ℓ E) (C.X q))
    (heC : Nonempty
      (((CondensedRing.upperStar
        (SmallAdicCompletion.Coefficients.integerRing ℓ E) f).mapDerivedCategory).obj K ≅
        (condensedIntegralCriterionRealization ℓ
          (SmallAdicCompletion.Coefficients.field.{u} ℓ E) Y).obj C)) :
    ∃ (P : CochainComplex (ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) ℤ)
      (b c : ℤ),
      P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
      (∀ q, Module.Free (integralHeartScalars.{u} ℓ E) (P.X q) ∧
        Module.Finite (integralHeartScalars.{u} ℓ E) (P.X q)) ∧
      Nonempty
        (((CondensedRing.upperStar
          (SmallAdicCompletion.Coefficients.integerRing ℓ E) f).mapDerivedCategory).obj K ≅
          DerivedCategory.Q.obj
            (((integralHeartRealization.{u} ℓ E Y).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      ∀ q, Module.Finite (integralHeartScalars.{u} ℓ E) (P.homology q) ∧
        Nonempty ((CondensedRing.upperStar
          (SmallAdicCompletion.Coefficients.integerRing ℓ E) f).obj
            ((DerivedCategory.homologyFunctor _ q).obj K) ≅
              (integralHeartRealization.{u} ℓ E Y).obj (P.homology q)) := by
  let Λ := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  obtain ⟨eC⟩ := heC
  obtain ⟨P, hPb, hPc, hP, ⟨eP⟩⟩ :=
    integralHeart_scalarComplex_coordinates ℓ E C b c hb hc hC
  obtain ⟨e⟩ := integralHeart_pointScalar_comparison.{u} ℓ E
  let G := (upperStarFromPoint Y).mapMod Λ
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
      AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
    dsimp [pointUpperStar, Functor.sheafPullbackConstruction.sheafPullback]
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint Y) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : PreservesFiniteLimits G := by
    dsimp [G]
    infer_instance
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  let : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  obtain ⟨eReal⟩ := localModel_realization_iso ℓ E Y C P eP e
  have heK : Nonempty
      (((CondensedRing.upperStar
        (SmallAdicCompletion.Coefficients.integerRing ℓ E) f).mapDerivedCategory).obj K ≅
          DerivedCategory.Q.obj
            (((integralHeartRealization.{u} ℓ E Y).mapHomologicalComplex (.up ℤ)).obj P)) :=
    ⟨eC ≪≫ DerivedCategory.Q.mapIso eReal⟩
  refine ⟨P, b, c, hPb, hPc, hP, heK, ?_⟩
  intro q
  have : Module.Finite (integralHeartScalars.{u} ℓ E) (P.X q) := (hP q).2
  refine ⟨scalarHomology_finite P q, ?_⟩
  exact scalarModel_homology ℓ E f K P heK q


private theorem localModel_finiteFree
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (hK : constantModelBoundedConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X K) :
    integralHeartFiniteFreeLocalModel.{u} ℓ E X K := by
  let E₀ := SmallAdicCompletion.Coefficients.field.{u} ℓ E
  have hpid := (Padic.extension_integers_dvr ℓ E₀
    (Padic.coefficientExtensionAbsoluteValue ℓ E₀)
    (spectralNorm_extends (K := Padic ℓ) (L := E₀))).choose_spec.choose_spec
  have : IsPrincipalIdealRing (SmallAdicCompletion.Coefficients.integers.{u} ℓ E) :=
    hpid.2.2.2.2.2.2.2.2.1
  have : IsNoetherianRing (integralHeartScalars.{u} ℓ E) :=
    isNoetherianRing_of_ringEquiv (SmallAdicCompletion.Coefficients.integers.{u} ℓ E)
      ULift.ringEquiv.symm
  obtain ⟨S, hS⟩ :=
    ((condensed_integral_criterion ℓ E₀ X K).out 0 2).mp hK
  let T := S.toFiniteLocallyClosed
  have hTc : ∀ a : Fin T.n, Topology.IsConstructible (T.stratum a) :=
    S.isConstructible_stratum
  have hT : ∀ a : Fin T.n,
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (T.domain a), ∀ i : U.I₀,
        ∃ (C : CochainComplex
          (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
            (DerivedNakayama.integerRing ℓ E₀)) ℤ) (b c : ℤ),
          C.IsStrictlyGE b ∧ C.IsStrictlyLE c ∧
          (∀ q, Mod.IsFree (DerivedNakayama.integerRing ℓ E₀) (C.X q)) ∧
          Nonempty
            (((CondensedRing.upperStar (DerivedNakayama.integerRing ℓ E₀)
              (U.f i ≫ T.immersion a)).mapDerivedCategory).obj K ≅
                (condensedIntegralCriterionRealization ℓ E₀ (U.X i)).obj C) := hS
  clear_value T
  refine ⟨T, hTc, ?_⟩
  intro a
  obtain ⟨U, hU⟩ := hT a
  refine ⟨U, ?_⟩
  intro i
  obtain ⟨C, b, c, hb, hc, hC, ⟨eC⟩⟩ := hU i
  exact localModel_chart ℓ E (U.f i ≫ T.immersion a) K C b c hb hc hC ⟨eC⟩

/-- Integral constructible complexes admit finite free local models; their
cohomology is derived complete and constructible, and good truncations remain
constructible.

Source: blueprint latest, integral-heart-local-model, clauses (1)--(3),
and Stacks Tags 099I, 09C7, 09C4, 0990, 099Q and 099Y
(blueprint: det-lem-int-integral-heart-local-model).

Proof: the integral criterion supplies one stratification and pro-etale covers with
bounded finite free condensed complexes. Choose finite scalar coordinates in each degree;
fullness lifts the differentials, and faithfulness reflects their square-zero identities.
The constant-module sheafification and internal continuous scalar realizations are
naturally isomorphic, by their common adjunction to sections at the point. Pull back this
comparison and localize to obtain the required ordinary scalar models without changing
charts or degree bounds. Exact realization and exact inverse image commute with homology,
so their canonical comparison isomorphisms identify restricted cohomology with realized
scalar homology. Cycles embed in a finite term over the Noetherian coefficient DVR, and
homology is their quotient, hence finite.
For cohomology placed in degree zero, its only nonzero homology is the original
constructible cohomology sheaf. Constructible-module completeness supplies derived
completeness. Finally the homology formulas for good truncations preserve the original
constructibility property, while their standard bounds give boundedness.
-/
theorem integralHeartLocalModel
    (k₀ : Type u) [Field k₀] (p : ℕ) [CharP k₀ p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : p ≠ ℓ)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k₀))]
    [IsSeparated (X ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
    [QuasiCompact (X ↘ Spec (.of k₀))]
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (hK : constantModelBoundedConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X K) :
    integralHeartFiniteFreeLocalModel.{u} ℓ E X K ∧
      (∀ q : ℤ,
        SmallAdicCompletion.IsDerivedComplete ℓ E X
            (integralHeartCohomology.{u} ℓ E X K q) ∧
        constantModelBoundedConstructible
          (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
          (integralHeartCohomology.{u} ℓ E X K q)) ∧
      (∀ q : ℤ,
        constantModelBoundedConstructible
          (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
          ((DerivedCategory.TStructure.t.truncLE q).obj K) ∧
        constantModelBoundedConstructible
          (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
          ((DerivedCategory.TStructure.t.truncGE q).obj K)) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k₀))
  let : CompactSpace X := inferInstance
  let : QuasiSeparatedSpace X := inferInstance
  exact ⟨localModel_finiteFree ℓ E X K hK,
    localModel_cohomology_truncations ℓ E X K hK⟩

end AlgebraicGeometry.ProEtale
