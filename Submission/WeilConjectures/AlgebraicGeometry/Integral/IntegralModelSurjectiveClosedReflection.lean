/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Submission.WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Reflection of integral finite constant models across surjective closed immersions

Source: Stacks Project, Tags 09AB and 09BK; blueprint main-20261015,
`det-lem-int-ext-formula`, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The condensed valuation ring of the finite p-adic extension, with continuous-function
sections and the topology of the unique extending spectral absolute value. This merely
specializes the existing continuous coefficient construction.
Source: blueprint det-lem-int-ext-formula, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection). -/
noncomputable def integralModelCondensedCoefficients (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  letI := spectralNorm.normedField (Padic l) E
  Mon.mk (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E))

/-- The integral condensed coefficient ring is commutative, by its pointwise operations.
Source: blueprint det-lem-int-ext-formula, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection). -/
noncomputable instance integralModelCondensedCoefficients_isCommMonObj
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    IsCommMonObj (integralModelCondensedCoefficients l E).X :=
  letI := spectralNorm.normedField (Padic l) E
  inferInstanceAs (IsCommMonObj
    (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)))

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  CondensedRing.upperStarComp upperStarFromPointComp
  Mod.extendScalarsIsoComapInv

private theorem pointModelPullback {S T : Scheme.{u}} (f : S ⟶ T)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty ((CondensedRing.upperStar Λ f).obj
      (((upperStarFromPoint T).mapMod Λ).obj P) ≅
        ((upperStarFromPoint S).mapMod Λ).obj P) := by
  let φ := condensedPullbackHom Λ f
  let N := ((upperStarFromPoint S).mapMod Λ).obj P
  let e := (Functor.mapModCompIso (upperStarFromPoint T) (upperStar Ab.{u + 1} f)
    (upperStarFromPointComp f).hom Λ).app P
  exact ⟨(Mod.extendScalars φ).mapIso e ≪≫
    (Mod.extendScalarsIsoComapInv φ).app ((Mod.comap φ).obj N) ≪≫
      (Mod.comapEquivalenceOfIsIso φ).unitIso.symm.app N⟩

-- Keep the composition comparison abstract when applying it to chosen pullback maps.
private theorem exists_pullback_cover {X Z : Scheme.{u}} (i : Z ⟶ X)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X) :
    ∃ B : Scheme.Cover.{u} Scheme.proetalePrecoverage Z,
      ∃ (a : B.I₀ → C.I₀) (q : ∀ b, B.X b ⟶ C.X (a b)),
        ∀ b, B.f b ≫ i = q b ≫ C.f (a b) := by
  refine ⟨C.pullback₁ i, id, fun b ↦ pullback.snd i (C.f b), fun b ↦ ?_⟩
  exact pullback.condition

end AlgebraicGeometry.ProEtale
