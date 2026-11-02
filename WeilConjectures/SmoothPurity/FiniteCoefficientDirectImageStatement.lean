/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Finite coefficient change for ordinary direct image

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/lem-coef-finite-direct-image.md
(blueprint: lem-coef-finite-direct-image).

This module states the isomorphism clauses on the étale site and on the finite
constructible pro-étale realization, over a finite or algebraically closed base field
of characteristic `p > 0`, `p ≠ ell`. The canonical maps are the components of
`AlgebraicGeometry.FiniteCoefficientOrdinary.directImageMaps`. Their naturality in `K`
is the naturality field of these natural transformations. The composition and
successive-coefficient clauses, on both sites, hold for arbitrary rings and are the
existing theorems `FiniteCoefficientOrdinary.etale_composition`,
`FiniteCoefficientOrdinary.etale_coefficientComposition`,
`FiniteCoefficientOrdinary.proetale_composition` and
`FiniteCoefficientOrdinary.proetale_coefficientComposition` of the imported module;
they are not restated here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor
open AlgebraicGeometry

/-- The ordinary étale finite-coefficient projection is an isomorphism in the
finite-or-algebraically-closed field setting of the blueprint.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/lem-coef-finite-direct-image.md and its proof
`lem-coef-finite-direct-image.proof.md`, first paragraph
(blueprint: lem-coef-finite-direct-image).

Proof steps: (1) choose an ell-power annihilator for A; finite A and the
finite A-module B are finite and the finite-type separated morphism has a
uniform torsion cohomological bound (with the empty-source bound allowed).
(2) Finite A is Noetherian, hence B is finitely presented; truncate a
finite-free resolution of B and apply the finite-constant projection formula
to the bounded-above complex K. (3) Use the finite Tor interval of K to put
the scalar extension and its direct image in the required bounded-below
categories; the scalar-adjunction mate equation identifies its restriction
with that projection map. (4) Restriction of scalars is exact and
conservative, so the canonical B-linear mate is an isomorphism and its
naturality follows from the same counit and tensor comparisons. (5) The
direct-image output remains bounded constructible with finite Tor amplitude.
(6) Pasting the pullback/tensor comparisons and the direct-image compositor
proves geometric composition. (7) Reassociating three derived scalar
extensions proves the coefficient-chain identity. (8) The canonical
étale/pro-étale comparison square transports the isomorphism and all these
identities to the finite constructible pro-étale realization. -/
theorem finiteCoefficientDirectImageMap_isIso_general
    (k : Type u) [Field k] (p ell : ℕ) (_hp : 0 < p) [Fact ell.Prime]
    (_hchar : CharP k p) (_hellp : ell ≠ p) (_hk : Finite k ∨ IsAlgClosed k)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ r : ℕ, (ell ^ r : A) = 0)
    (B : Type (u + 1)) [CommRing B] [Algebra A B] [Module.Finite A B]
    (T X : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : T ⟶ X) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left]
    (K : AlgebraicGeometry.Etale.DerivedCategoryModule A T.left)
    (_hK : AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A T.left K)
    (_hTor : ∃ a b : ℤ, a ≤ b ∧
      AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn A T.left a b K) :
    IsIso ((AlgebraicGeometry.FiniteCoefficientOrdinary.directImageMaps.etale
      (algebraMap A B) f.left).app K) := by
  sorry

/-- The finite constructible pro-étale realization has the same coefficient
projection isomorphism.

Source: the pro-étale clause of the blueprint unit
literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/lem-coef-finite-direct-image.md, proof second paragraph
(blueprint: lem-coef-finite-direct-image).

Proof (node Step 8): a separated finite-type morphism is qcqs and `K`, `K_B` are
bounded below (Steps 3 and 5). The canonical étale/pro-étale comparison square
commutes with scalar extension and both counits; its direct-image comparisons are
invertible on these bounded-below complexes, as are the scalar/tensor comparisons,
so the étale isomorphism of `finiteCoefficientDirectImageMap_isIso_general`
transports to this map. Finite coefficient rings keep the same Tor intervals under
the realization. -/
theorem finiteCoefficientDirectImageMap_proEtale_isIso_general
    (k : Type u) [Field k] (p ell : ℕ) (_hp : 0 < p) [Fact ell.Prime]
    (_hchar : CharP k p) (_hellp : ell ≠ p) (_hk : Finite k ∨ IsAlgClosed k)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ r : ℕ, (ell ^ r : A) = 0)
    (B : Type (u + 1)) [CommRing B] [Algebra A B] [Module.Finite A B]
    (T X : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : T ⟶ X) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left]
    (K : AlgebraicGeometry.Etale.DerivedCategoryModule A T.left)
    (_hK : AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A T.left K)
    (_hTor : ∃ a b : ℤ, a ≤ b ∧
      AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn A T.left a b K) :
    IsIso ((AlgebraicGeometry.FiniteCoefficientOrdinary.directImageMaps.proetale
      (algebraMap A B) f.left).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T.left).mapDerivedCategory.obj K)) := by
  sorry
