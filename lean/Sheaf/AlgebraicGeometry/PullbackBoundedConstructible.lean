/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Sheaf.Paper.CompleteCoefficientDatum
public import Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Pullback preserves bounded constructibility and cohomological intervals

Source: Weil conjectures blueprint, proper base change, node order 1303;
Stacks, Tags 09AK, 09AL and 09B5
(blueprint: lem-weil-pbc-pullback-preserves-bounded-constructible).

The coefficient categories and the essential-image predicate are the recorded
`FiniteCoefficientDerivedCategory` and `isBoundedConstructibleFiniteCoefficient`.
The auxiliary closure and preservation statements expose precisely the structures
needed to name the canonical restriction; their arguments work for every finite
commutative ring. The main statement retains the specified adic quotients `P_n`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The full essential image of bounded constructible etale complexes is triangulated.
Source: blueprint order 1303, proof, final paragraph; Stacks, Tags 09AL and 09B5
(blueprint: lem-weil-pbc-pullback-preserves-bounded-constructible).

Proof: etale bounded constructible complexes form a triangulated subcategory by
`prop-constructible-derived-subcategory`. The exact comparison is triangulated and
fully faithful on bounded below complexes (`thm-weil-pbc-site-comparison`). Lift a map
between two essential-image objects to a map of bounded constructible etale witnesses.
The cone of that map is bounded constructible. Its comparison image is a cone of the
original map. The etale shift and zero likewise give witnesses for shifts and zero.
Transport through the canonical coefficient realization preserves these statements. -/
theorem isBoundedConstructibleFiniteCoefficient_isTriangulated (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (isBoundedConstructibleFiniteCoefficient T Λ).IsTriangulated := by
  sorry

attribute [instance] isBoundedConstructibleFiniteCoefficient_isTriangulated

/-- Exact inverse image preserves the recorded essential-image constructibility.
Source: blueprint order 1303, proof, first three paragraphs
(blueprint: lem-weil-pbc-pullback-preserves-bounded-constructible).

Proof: choose a bounded constructible etale witness L for K. Exactness identifies
cohomology of termwise etale inverse image with inverse image of cohomology: cycles
are kernels, boundaries are kernels of cokernels, and cohomology is their quotient.
Pull back each finite constructible stratification of H^i(L). The underlying finite
locally constant set sheaf remains so by `lem-weil-pbc-constructible-etale-set-pullback`.
Trivialize its module structure by a finite refinement on which the addition, zero,
negation and scalar multiplication tables are constant. Finiteness of both the ring
and the stalk set makes this refinement finite. Thus the etale pullback is bounded
constructible. Apply `lem-weil-pbc-comparison-pullback` in every degree; naturality
for the differentials makes these component isomorphisms an isomorphism of complexes.
Exact termwise descent gives the derived comparison isomorphism, exhibiting the
pulled-back K as the comparison image of the pulled-back L. -/
theorem finiteCoefficientDerivedPullback_preserves_boundedConstructible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (K : FiniteCoefficientDerivedCategory Y Λ)
    (hK : isBoundedConstructibleFiniteCoefficient Y Λ K) :
    isBoundedConstructibleFiniteCoefficient X Λ
      ((finiteCoefficientDerivedPullback Y Λ f).obj K) := by
  sorry

/-- The restriction of exact termwise inverse image to the recorded bounded constructible
full subcategories, acting by the original derived functor on every morphism.
Source: blueprint order 1303
(blueprint: lem-weil-pbc-pullback-preserves-bounded-constructible). -/
noncomputable def finiteCoefficientBoundedConstructiblePullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    FiniteCoefficientBoundedConstructibleDerivedCategory Y Λ ⥤
      FiniteCoefficientBoundedConstructibleDerivedCategory X Λ :=
  (isBoundedConstructibleFiniteCoefficient X Λ).lift
    ((isBoundedConstructibleFiniteCoefficient Y Λ).ι ⋙
      finiteCoefficientDerivedPullback Y Λ f)
    (fun K ↦ finiteCoefficientDerivedPullback_preserves_boundedConstructible f Λ K.obj K.property)

/-- The restriction carries the shift comparison of exact termwise inverse image.
Source: blueprint order 1303, proof, last paragraph
(blueprint: lem-weil-pbc-pullback-preserves-bounded-constructible). -/
noncomputable instance finiteCoefficientBoundedConstructiblePullback_commShift
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientBoundedConstructiblePullback f Λ).CommShift ℤ :=
  inferInstanceAs (((isBoundedConstructibleFiniteCoefficient X Λ).lift
    ((isBoundedConstructibleFiniteCoefficient Y Λ).ι ⋙
      finiteCoefficientDerivedPullback Y Λ f)
    (fun K ↦ finiteCoefficientDerivedPullback_preserves_boundedConstructible
      f Λ K.obj K.property)).CommShift ℤ)

/-- For the specified finite perfect adic quotient P_(n+1), derived pullback restricts to
an exact triangulated functor on bounded constructible pro-etale complexes and preserves
every cohomological interval. The use of n+1 ranges over precisely all positive indices.
Source: blueprint order 1303; Stacks, Tags 09AK, 09AL and 09B5
(blueprint: lem-weil-pbc-pullback-preserves-bounded-constructible).

Proof: the preceding preservation statement uses the etale origin of K, exact etale
inverse image, finite module-operation tables on pulled-back strata, and the natural
comparison isomorphism degree by degree. The preceding triangulated-closure statement
lifts maps to etale witnesses using bounded-below full faithfulness, then takes their
etale cones; etale shifts and zero give the other closure operations. The ambient
pullback is the localization of exact termwise module inverse image, hence commutes
with shifts and preserves distinguished triangles. These structures restrict to the
full subcategories preserved above, proving exact triangulatedness. Finally exactness
identifies H^i(Lg^*K) with g^-1 H^i(K): kernels give cycles, kernels of cokernels give
boundaries, and their quotient gives cohomology. Additivity sends the zero sheaf to
zero. Thus each degree outside [a,b] that vanishes for K vanishes after pullback.
No condition on the morphism g or on either scheme is used. -/
theorem finiteCoefficientBoundedConstructiblePullback_exact_and_interval
    (A : Type v) [CommRing A] (d : Scheme.CompleteCoefficientDatum A)
    [∀ m : ℕ, Finite (A ⧸ d.ideal ^ (m + 1))] (n : ℕ)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (_e : Λ ≃+* A ⧸ d.ideal ^ (n + 1)) {V' V : Scheme.{u}} (g : V' ⟶ V) :
    (finiteCoefficientBoundedConstructiblePullback g Λ).IsTriangulated ∧
    ∀ (K : FiniteCoefficientBoundedConstructibleDerivedCategory V Λ) (a b : ℤ),
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero
        ((_root_.DerivedCategory.homologyFunctor (FiniteCoefficientModules V Λ) i).obj K.obj)) →
      ∀ i : ℤ, (i < a ∨ b < i) → IsZero
        ((_root_.DerivedCategory.homologyFunctor (FiniteCoefficientModules V' Λ) i).obj
          ((finiteCoefficientBoundedConstructiblePullback g Λ).obj K).obj) := by
  sorry

end AlgebraicGeometry.ProEtale
