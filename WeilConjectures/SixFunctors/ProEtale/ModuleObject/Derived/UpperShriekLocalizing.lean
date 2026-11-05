/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Basic
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.CategoryTheory.Triangulated.IdempotentCompleteOfCoproducts
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Subobject.WellPowered
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.LeftTExact
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionDerived
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
public import Mathlib.LinearAlgebra.TensorProduct.Tower
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# The exceptional inverse image on `Loc(Dᵇc)`, `ℓ`-adic coefficients

Let `Λ` be a commutative condensed ring. For a scheme `X` the localizing closure
`Loc(Dᵇc(X)⟦Λ⟧)` (blueprint `sk-def-localizing-closure`) is the smallest triangulated
subcategory of `D(X_proét, Λ_X)` (module objects over `Λ_X = p_X^* Λ`) containing the bounded
constructible complexes `Dᵇc(X)⟦Λ⟧` and closed under direct sums
(`AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible`). For the `ℓ`-adic
coefficient rings `Λ = 𝒪_E, E, ℚ̄_ℓ` (`ℤ_ℓ` and `ℚ_ℓ` being the case `E = ℚ_ℓ`), one has
`Dctf(X, Λ) = Dᵇc(X, Λ)`, so this is the blueprint's `Loc(Dctf(X, Λ))`.

For a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f : X ⟶ Y` such that `Rf_!(c)⟦Λ⟧` maps
`Loc(Dᵇc(X)⟦Λ⟧)` into `Loc(Dᵇc(Y)⟦Λ⟧)`, its restriction is the functor
`Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)`
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekLocalizing`). Under the
hypotheses of Brown representability (blueprint `sk-lem-brown-hypotheses`) and the properties of
`Rf_!(c)` of blueprint `det-sf-comp-coherence-single`, it has an exact right adjoint `f^!`,
which preserves direct sums and is unique up to unique isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_rightAdjoint_rightDerivedLowerShriekLocalizing`,
blueprint `sk-prop-sf-existence`). This is uniform in `Λ`.

For the three families of `ℓ`-adic coefficient rings, schemes separated of finite type over a
field `k` in which `ℓ` is invertible and which is finite or separably closed (so that
`cd_ℓ(k)` is finite; without this, the compact generation fails, e.g. for `k = ℝ`), the two
inputs are the theorems

| `Λ` | `sk-lem-brown-hypotheses` | `det-sf-comp-coherence-single` |
| --- | --- | --- |
| `E` | `compactlyGenerates_continuousMapRingObj` | `lowerShriek_continuousMapRingObj` |
| `𝒪_E` | `compactlyGenerates_padicIntegersRingObj` | `lowerShriek_padicIntegersRingObj` |
| `ℚ̄_ℓ` | `compactlyGenerates_padicAlgClRingObj` | `lowerShriek_padicAlgClRingObj` |

(all in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizingEllAdic`), and the
existence theorem follows. The finite coefficient rings are treated in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing`.

## The formal reductions

For `sk-lem-brown-hypotheses`, on a separated finite-type (hence noetherian) `k`-scheme `X`:
`Loc(Dᵇc(X)⟦Λ⟧)` is idempotent complete, as is any pretriangulated category with countable
coproducts (`ObjectProperty.isIdempotentComplete_localizingClosure`); `Dᵇc(X)⟦Λ⟧` is stable under
shifts, so its objects detect zero objects of `Loc(Dᵇc(X)⟦Λ⟧)`
(`ObjectProperty.isZero_of_forall_eq_zero_localizingClosure`); and it is essentially small, its
objects being iterated extensions of shifted constructible sheaves
(`exists_skeleton_boundedConstructible`). What remains is the compactness of the bounded
constructible complexes in `Loc(Dᵇc(X)⟦Λ⟧)` (`compactlyGenerates_of_isCompactObj`), which reduces
to that of the constructible sheaves.

For `det-sf-comp-coherence-single`, with `X̄` noetherian: `j_!` is exact and preserves direct sums,
so it maps `Dᵇc` into `Dᵇc`, as it maps constructible sheaves to constructible sheaves
(`isConstructibleModuleObject_openImmersionLowerShriek_obj`), and then
`Loc` into `Loc` (`localizingBoundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj`);
the composite `Rp_* ∘ j_!` then has the required properties as soon as `Rp_*` does
(`lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses`).
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Blueprint `sk-def-localizing-closure`: the localizing closure `Loc(Dᵇc(X)⟦Λ⟧)`, the smallest
triangulated subcategory of `D(X_proét, Λ_X)` closed under isomorphisms and direct sums which
contains the bounded constructible complexes. For the `ℓ`-adic coefficient rings these are the
blueprint's `Dctf(X, Λ)`. -/
noncomputable abbrev localizingBoundedConstructible (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  (boundedConstructible (condensedRingObj Λ X)).localizingClosure

/-- The derived category `D(X_proét, Λ_X)` of module objects has direct sums. -/
instance hasCoproducts_derivedCategory (X : Scheme.{u}) :
    HasCoproducts.{u + 1} (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) := by
  intro J
  have : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  exact DerivedCategory.hasColimitsOfShape_discrete J

section General

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The properties of the compact-support direct image `Rf_!(c)⟦Λ⟧ = Rp_* ∘ j_!` along a
compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of blueprint `det-sf-comp-coherence-single`: it maps
`Loc(Dᵇc(X)⟦Λ⟧)` into `Loc(Dᵇc(Y)⟦Λ⟧)` and `Dᵇc(X)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧`, and its restriction
to `Loc(Dᵇc(X)⟦Λ⟧)` preserves direct sums. -/
def LowerShriekLocalizingHypotheses : Prop :=
  (∀ K, localizingBoundedConstructible Λ X K →
    localizingBoundedConstructible Λ Y ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
  (∀ K, boundedConstructible (condensedRingObj Λ X) K →
    boundedConstructible (condensedRingObj Λ Y)
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
  ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
    ((localizingBoundedConstructible Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)

variable {Λ c} (hc : LowerShriekLocalizingHypotheses Λ c)

end General

/-! ### Reduction to the coefficient-specific inputs -/

section Reduction

/-- The bounded constructible complexes are stable under shifts: `Hᵃ(K⟦n⟧) ≅ Hⁿ⁺ᵃ(K)`. -/
instance isStableUnderShift_boundedConstructible (X : Scheme.{u}) :
    (boundedConstructible (condensedRingObj Λ X)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ ⟨DerivedCategory.TStructure.t.bounded.le_shift n K hK.1,
    fun a ↦ IsConstructibleModuleObject.of_iso
      (((DerivedCategory.homologyFunctor _ 0).shiftIso n a (n + a) rfl).app K).symm (hK.2 (n + a))⟩⟩

/-- Constructibility of module objects is invariant under isomorphisms. -/
instance isClosedUnderIsomorphisms_isConstructibleModuleObject (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstructibleModuleObject (condensedRingObj Λ X)) where
  of_iso e h := IsConstructibleModuleObject.of_iso e h

/-- The extension by zero `j_!` along an open immersion preserves direct sums. -/
instance preservesColimitsOfShape_mapDerivedCategory_openImmersionLowerShriek {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) D((j)_!open⟦Λ⟧) := by
  have (T : Scheme.{u}) : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  have : HasColimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  have : PreservesColimitsOfSize.{u + 1, u + 1} (j)_!open⟦Λ⟧ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).leftAdjoint_preservesColimits
  exact Functor.preservesColimitsOfShape_mapDerivedCategory _ J

end Reduction

end AlgebraicGeometry.ProEtale.CondensedRing
