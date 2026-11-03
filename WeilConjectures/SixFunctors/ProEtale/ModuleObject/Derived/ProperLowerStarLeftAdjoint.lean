/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegralDerivedLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegralTransport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarTwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RationalProperLowerStarAdjoint
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.CoherentReduction.ProperTorsionAdjunctionRealization
import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentMappingSystems
import WeilConjectures.AlgebraicGeometry.FiniteProperQuotient.FiniteExceptionalDerivedHom
import WeilConjectures.AlgebraicGeometry.CoherentReduction.FiniteProperReductionTransport
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentIntegralReduction
import Mathlib.Algebra.Field.ULift
import Mathlib.Condensed.TopComparison
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperQlbarAdjointOfFiniteCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizedDirectImageComparison

/-!
# The proper direct image on `Dᵇc` is a left adjoint, over any field

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. For a proper morphism
`g : Z ⟶ Y` of separated `k`-schemes of finite type, the derived pushforward
`Rg_* : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` is a left adjoint, for each of the `ℓ`-adic coefficient rings
`Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` (blueprints `lem-sfb-dc-proper-pushforward-left-adjoint-oe`,
`lem-sfb-dc-proper-pushforward-left-adjoint-e`, `lem-sfb-dc-proper-pushforward-left-adjoint-qlbar`):

* `isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj`,
* `isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj`, from the case
  of `𝒪̲_E` by inverting `ℓ`
  (`isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj_of_padicIntegersRingObj`),
* `isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`, from the case of
  the `E̲` by the 2-colimit argument
  (`isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_forall`).

No assumption on `k` is made: these do not use Brown representability on the localizing closures,
which needs `cd_ℓ(k) < ∞`.

These instances are the input of the exceptional inverse image `Rg^!` on `Dᵇc` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- Blueprint `lem-sfb-dc-proper-pushforward-left-adjoint-oe`: for a proper morphism
`g : Z ⟶ Y` and a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived pushforward
`Rg_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` is a left adjoint (SGA 4 XVIII, 3.1.4; SGA 4½,
[Th. finitude]; Bhatt–Scholze, Section 6.8). -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E g).IsLeftAdjoint :=
  isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_finiteIntermediateField ℓ g
    (fun E' ↦
      isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_isProper' ℓ E' g) E

/-- Proper pushforward with finite-extension coefficients has a right adjoint.
Source: inversion-of-ell step of the current blueprint proper-adjoint proof
(blueprint: sk-def-sfb-dc-upper-shriek). -/
instance isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [IsProper g.left] :
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g).IsLeftAdjoint :=
  isLeftAdjoint_finiteCoefficients ℓ g E

/-- Proper pushforward with algebraic-closure coefficients has a right adjoint.
Use the current proper-adjoint theorem on its stated finite/algebraically closed domain;
for other fields descend the finite-extension adjunctions along coefficient enlargement.
Source: current blueprint proper-adjoint theorem and its finite-coefficient descent step
(blueprint: sk-def-sfb-dc-upper-shriek). -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj [IsProper g.left] :
    (boundedConstructibleLowerStar ℓ g).IsLeftAdjoint := by
  classical
  by_cases hk : Finite k ∨ IsAlgClosed k
  · exact properPushforwardLeftAdjointQlbar ℓ hk g
  · exact properPushforwardLeftAdjointQlbar_of_finiteCoefficients ℓ g
      (fun E ↦ isLeftAdjoint_finiteCoefficients ℓ g E)

end AlgebraicGeometry.ProEtale.CondensedRing
