/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.LeftTExact
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionDerived
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
import Mathlib.Algebra.Homology.Embedding.IsSupported
import Mathlib.Algebra.Homology.Embedding.Restriction
import WeilConjectures.AlgebraicGeometry.Modules.FreeMatrix
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexLocus
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
import WeilConjectures.Mathlib.RingTheory.Flat.Stability
import WeilConjectures.AlgebraicGeometry.Modules.DescentEffective
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
import Mathlib.Algebra.Module.Presentation.Finite
import Mathlib.Algebra.Module.Presentation.Tensor
import WeilConjectures.Compactification.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Curve.FunctionFieldCohomology
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GeometricFiber
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.AlgebraicGeometry.AffineSpace.Line
import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
import WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.Grothendieck
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import WeilConjectures.Compactification.Dense
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
import WeilConjectures.AlgebraicGeometry.FiniteOverField
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.LeftTExact
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionDerived
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import WeilConjectures.AlgebraicGeometry.Modules.FreeMatrix
public import WeilConjectures.AlgebraicGeometry.Modules.HomSection
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexLocus
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Finite
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.Mathlib.RingTheory.Flat.Stability
public import WeilConjectures.AlgebraicGeometry.Modules.DescentEffective
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack
public import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
public import Mathlib.Algebra.Module.Presentation.Finite
public import Mathlib.Algebra.Module.Presentation.Tensor
public import WeilConjectures.Compactification.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Curve.FunctionFieldCohomology
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GeometricFiber
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Line
public import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.Grothendieck
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
public import WeilConjectures.AlgebraicGeometry.FiniteOverField
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite

import WeilConjectures.AlgebraicGeometry.EllAdicProperConstructibleCohomology
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperBoundedBelowCoproducts

/-!
# The proper direct image for the `ℓ`-adic coefficient rings: the inputs

Let `ℓ` be a prime, `k` a field in which `ℓ` is invertible, and `p : Z ⟶ Y` a proper morphism to
a noetherian `k`-scheme. For the `ℓ`-adic condensed coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ`, the
properties of the derived direct image `Rp_*` on module objects over `Λ` used for the
compact-support direct image on `Loc(Dᵇc)` (blueprint `det-sf-comp-coherence-single`) are:

* `Rp_*` maps `Dᵇc(Z)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧` (blueprint `sk-thm-sfb-proper-base-change`):
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj`,
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj`,
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj`;
* for `Y` separated of finite type over `k`, `Rp_*` has finite amplitude on the
  ind-constructible heart and commutes with direct sums there
  (`AlgebraicGeometry.ProEtale.CondensedRing.ProperLowerStarHeartHypotheses`, blueprints
  `sk-lem-proper-heart-bound` for `E` and `ℚ̄_ℓ`, `det-prop-int-compactness-direct-sums` (1) for
  `𝒪_E`): `properLowerStarHeartHypotheses_continuousMapRingObj`,
  `properLowerStarHeartHypotheses_padicIntegersRingObj`,
  `properLowerStarHeartHypotheses_padicAlgClRingObj`.

From the latter, the restriction of `Rp_*` to `Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums
(`AlgebraicGeometry.ProEtale.CondensedRing.ProperLowerStarHeartHypotheses.preservesColimitsOfShape`,
blueprint `det-prop-int-compactness-direct-sums` (2), (3), proved by dévissage and left
completeness).

The finiteness of `Rp_*` on `Dᵇc` is reduced to residue field coefficients
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness`):
over a noetherian base this uses the finiteness theorem for proper morphisms with torsion
coefficients over a noetherian base
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`),
and over a base of finite type over `k` the proved finite type case
(`boundedConstructible_rightDerivedLowerStar_of_isProper_*_of_finiteType`). The heart hypotheses
follow from the ind-constructible heart (`isIndConstructibleHeart_*`), the continuity of `Rp_*`
(`properLowerStarHeartHypotheses_of_isIndConstructibleHeart`) and a uniform bound on
constructible sheaves
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicBound`); the
ind-constructible heart is stated for separated `k`-schemes of finite type (the setting of the
blueprint), hence the finite type hypotheses on `Y`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]

/-! ### The coefficient ring `E` -/

/-! ### The coefficient ring `𝒪_E` -/

/-- Blueprint `sk-thm-sfb-proper-base-change` (`det-thm-sfb-proper-base-change-integral` (1)):
for the coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a proper morphism
`p : Z ⟶ Y` to a noetherian `k`-scheme, `Rp_*` maps `Dᵇc(Z)⟦𝒪_E⟧` into `Dᵇc(Y)⟦𝒪_E⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {Z Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y] (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.padicIntegersRingObj.{u} ℓ E⟧).obj K) :=
  boundedConstructible_rightDerivedLowerStar_padicIntegersRingObj_of_residueField ℓ p E
    (residueFieldFiniteness_of_isNoetherian ℓ p aY) K hK

/-! ### The coefficient ring `ℚ̄_ℓ` -/

end AlgebraicGeometry.ProEtale.CondensedRing
