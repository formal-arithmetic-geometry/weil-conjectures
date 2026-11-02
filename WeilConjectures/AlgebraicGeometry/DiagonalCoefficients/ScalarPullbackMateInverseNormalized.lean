/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
import all WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization

/-! # The scalar pullback mate has a normalized inverse

Source: blueprint, diagonal tower coefficient changes, paragraph (3), last sentence;
scalar six-functor pullback, part (1).
(blueprint: lem-sfb-scalar-pullback-mate-inverse-normalized).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- These names abbreviate the same total derived functors used by the diagonal interface.
set_option allowUnsafeReducibility true in
attribute [local reducible] QuotientChange.D QuotientChange.L

/-- The prescribed scalar mate is the inverse of a counit-normalized balancing isomorphism.
The existential isomorphism states invertibility of the actual mate, and `PullNormalized`
fixes its inverse on every homotopy complex using the ordinary pure-tensor comparison.
No flatness or boundedness is assumed.

Source: blueprint, diagonal tower coefficient changes, paragraph (3), last sentence;
scalar six-functor pullback, part (1).
(blueprint: lem-sfb-scalar-pullback-mate-inverse-normalized).

Proof:
1. Install the Grothendieck abelian and derived-category instances on the module
   categories of `R` and `T` over every scheme, transported along
   `ModuleRingedComparison.equivalence`.
2. Apply `QuotientChange.internal_pull_normalization_exists` to obtain an isomorphism b
   satisfying `PullNormalized`.
3. The normalized inverse-mate calculation `QuotientChange.normalized_inverse` of the
   restriction-mate normalization module identifies b.inv with the inverse scalar mate,
   for `QuotientChange.scalarAdj a S` and `QuotientChange.scalarAdj a X`, of the inverse
   of the restriction square `QuotientChange.normalizationRestrictionPull a f`.
4. Unfolding `scalarPullbackComparison` (via `Adjunction.pushHomOfComapIso` and
   `scalarRestrictionPullbackIso`) gives the same inverse scalar mate of the same
   restriction square, so b.inv = `scalarPullbackComparison a f`. Return b with this
   equality and the normalization of step 2.
-/
theorem scalar_pullback_mate_inverse_normalized
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S) :
    ∃ b : QuotientChange.D a S ⋙ QuotientChange.L T f ≅
        QuotientChange.L R f ⋙ QuotientChange.D a X,
      b.inv = scalarPullbackComparison a f ∧ QuotientChange.PullNormalized a f b := by
  let _ : ∀ Z : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules R Z) := fun Z ↦
    IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence R Z)
  let _ : ∀ Z : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules T Z) := fun Z ↦
    IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence T Z)
  let _ : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules R Z) := fun Z ↦
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let _ : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules T Z) := fun Z ↦
    HasDerivedCategory.ofIsGrothendieckAbelian _
  obtain ⟨b, hb⟩ := QuotientChange.internal_pull_normalization_exists a f
  have h := QuotientChange.normalized_inverse a f b hb
  have he : scalarPullbackComparison a f = b.inv := by
    simpa only [scalarPullbackComparison, Adjunction.pushHomOfComapIso,
      scalarRestrictionPullbackIso, QuotientChange.normalizationRestrictionPull,
      QuotientChange.scalarAdj, QuotientChange.V, QuotientChange.V₀,
      QuotientChange.L, QuotientChange.D, QuotientChange.extension, id_eq,
      CondensedRing.moduleObjectDerivedPullback, derivedUpper, derivedScalars] using h.symm
  exact ⟨b, he.symm, hb⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
