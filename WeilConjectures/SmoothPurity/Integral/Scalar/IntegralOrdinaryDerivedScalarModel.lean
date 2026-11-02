/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # The ordinary derived scalar extension as a universal derived change of rings

Source: Stacks Tag 06YY; Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe d u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

private local instance (W : Scheme.{u}) : EssentiallySmall.{u+1} W.ProEt :=
  essentiallySmallSelf.{0, u, u+1} _

private local instance (W : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : Scheme.{u}) :
    (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

attribute [local irreducible] HasDerivedCategory.standard
  completedScalarChangeData
  integralOrdinaryScalar completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : Scheme.{u})

/-- Any isomorphism of the two ordinary scalar models lifts to an isomorphism of the
ordinary derived extension with the universal derived change of rings, compatible with
the cochain counits.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the exact ordinary functor induces a left derived functor of itself; the
universal derived change of rings is a left derived functor of the isomorphic model. -/
theorem integralOrdinaryDerivedScalar_completedModel
    (t : integralOrdinaryScalar l E L ι Y ≅ completedOrdinaryScalarExtension.{u, u} l E L ι Y) :
    ∃ e : integralOrdinaryDerivedScalar l E L ι Y ≅
        completedDerivedScalarExtension.{u, u} l E L ι Y,
      ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L ι Y P =
          (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P) := by
  let G := integralOrdinaryScalar l E L ι Y
  let q := HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)
  let D := completedScalarCochainModel.{u, u} l E L ι Y
  let T := completedDerivedScalarExtension.{u, u} l E L ι Y
  let t' := NatIso.mapHomologicalComplex t (.up ℤ)
  let ε : DerivedCategory.Q ⋙ T ⟶
      completedOrdinaryScalarComplex.{u, u} l E L ι Y ⋙ DerivedCategory.Q := D.ε
  let : T.IsLeftDerivedFunctor ε q := D.universal
  let : G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom q :=
    Functor.isLeftDerivedFunctor_of_inverts q _ G.mapDerivedCategoryFactors
  let e : integralOrdinaryDerivedScalar l E L ι Y ≅ T :=
    Functor.leftDerivedNatIso G.mapDerivedCategory T G.mapDerivedCategoryFactors.hom
      ε q (Functor.isoWhiskerRight t' DerivedCategory.Q)
  refine ⟨e, fun P ↦ ?_⟩
  have h : e.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P =
      G.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (t'.hom.app P) :=
    Functor.leftDerivedNatTrans_app G.mapDerivedCategory T
      G.mapDerivedCategoryFactors.hom ε q
      (Functor.isoWhiskerRight t' DerivedCategory.Q).hom P
  have hε : ε.app P = completedScalarCounit.{u, u} l E L ι Y P :=
    completedScalarCochainModel_counit l E L ι Y P
  exact (congrArg (e.hom.app (DerivedCategory.Q.obj P) ≫ ·) hε).symm.trans h

/-- Bounded constructible complete objects are derived complete in the unrestricted sense.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: derived completeness does not depend on the auxiliary finite field datum; compare
both data with the intrinsic augmented-tower predicate. -/
theorem isDerivedCompleteUnrestricted_of_boundedConstructible
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (K : completedIntegralDerivedCategory l E Y D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E Y K) :
    IsDerivedCompleteUnrestricted l E Y K := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let Δ : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_refl 1
      cardinality_eq := (pow_one p).symm
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl' : l ≠ Δ.p := by change l ≠ p; omega
  exact ⟨Δ, hl', (sfDerivedComplete_iff_legacy l E Y Δ hl' K).mp
    ((sfDerivedComplete_iff_legacy l E Y D hl K).mpr hK.1)⟩

end WeilConjectures
