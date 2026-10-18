/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# Finite affine factorizations and gluing of intervals

Source: the Weil conjectures blueprint, main-20261015, `sec-six-functors-basics`,
`sk-prop-sf-rf-shriek-preservation.proof.md`, opening and final paragraphs
(blueprint: lem-sf-affine-chart-factorization-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite affine charts factor through affine space, and local constructibility and
cohomological and Tor bounds glue with the minimum lower and maximum upper endpoints.
`IsLeast` and `IsGreatest` specify precisely these extrema of the finite endpoint ranges.
Restriction is the functor on derived categories induced by exact etale inverse image.
Source: main-20261015 blueprint, proof of `sk-prop-sf-rf-shriek-preservation`, first and last
paragraphs (blueprint: lem-sf-affine-chart-factorization-gluing).

Proof plan:
1. Choose finitely many affine opens of `Y` and, by quasi-compactness of `f`, finitely
   many affine opens of their inverse images (def-weil-finite-type-morphism).
2. Present each finite-type affine algebra as a quotient of a polynomial algebra;
   the quotient yields the closed immersion (def-weil-closed-immersion), with the
   standard affine-space projection (def-sbc-affine-space).
3. That projection is smooth of the specified relative dimension
   (sbc-lem-affine-space-smooth) and separated. Its finite polynomial generators,
   together with generators of the base algebra, give finite type over `k`.
   Affine sources are separated (lem-weil-pbc-affine-source-morphism-separated).
4. The scheme `X` is qcqs (lem-weil-pbc-qcqs-over-affine), and the charts are qcqs
   (lem-weil-pbc-affine-scheme-qcqs).
5. Open immersions are etale (lem-weil-pbc-etale-composition-cancellation).
   Exact inverse image commutes with cohomology
   (prop-weil-pbc-inverse-image-modules-exact), and its restriction comparison
   (lem-weil-pbc-etale-inverse-image-restriction) detects zero sheaves on the cover.
6. Glue constructibility by lem-weil-pbc-constructible-qcqs-affine-local. Outside
   the minimum and maximum endpoints, every restricted cohomology sheaf is zero;
   step 5 gives global vanishing, hence bounded constructibility.
7. For every degree-zero module sheaf, inverse image commutes with derived tensor
   (lem-kun-inverse-image-monoidal). Apply the same zero test to tensor cohomology
   to obtain the global Tor interval (def-kun-tor-amplitude).
8. On the empty scheme the empty covering forces every module sheaf to be zero.
   Thus `K` is zero, its cohomology and tensor cohomology vanish in every degree,
   and the empty stratification gives constructibility. No extrema are taken. -/
theorem exists_sf_affine_chart_factorization_gluing
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (n : ℕ) (V : Fin n → Y.Opens) (N : Fin n → ℕ)
      (U : (i : Fin n) → Fin (N i) → X.Opens)
      (hUV : ∀ (i : Fin n) (j : Fin (N i)), U i j ≤ f ⁻¹ᵁ V i)
      (m : (i : Fin n) → Fin (N i) → ℕ)
      (c : (i : Fin n) → (j : Fin (N i)) →
        (U i j).toScheme ⟶ AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme),
      (∀ i : Fin n, IsAffineOpen (V i)) ∧
      (∀ y : Y, ∃ i : Fin n, y ∈ V i) ∧
      (∀ (i : Fin n) (j : Fin (N i)), IsAffineOpen (U i j)) ∧
      (∀ (i : Fin n) (x : X), x ∈ f ⁻¹ᵁ V i → ∃ j : Fin (N i), x ∈ U i j) ∧
      (∀ (i : Fin n) (j : Fin (N i)),
        IsClosedImmersion (c i j) ∧
        c i j ≫ (AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) = f.resLE (V i) (U i j) (hUV i j) ∧
        SmoothOfRelativeDimension (m i j)
          (AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘ (V i).toScheme) ∧
        IsSeparated
          (AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘ (V i).toScheme)) ∧
      (∀ i : Fin n,
        IsSeparated ((V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        QuasiCompact ((V i).ι ≫ (Y ↘ Spec (.of k)))) ∧
      (∀ (i : Fin n) (j : Fin (N i)),
        IsSeparated ((U i j).ι ≫ (X ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((U i j).ι ≫ (X ↘ Spec (.of k))) ∧
        QuasiCompact ((U i j).ι ≫ (X ↘ Spec (.of k))) ∧
        IsSeparated ((AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) ≫ (V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) ≫ (V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        QuasiCompact ((AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) ≫ (V i).ι ≫ (Y ↘ Spec (.of k)))) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A]
        (K : Etale.DerivedCategoryModule A X)
        (r s a b : (Σ i : Fin n, Fin (N i)) → ℤ),
        (∀ (i : Fin n) (j : Fin (N i)),
          (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
            ((_root_.DerivedCategory.homologyFunctor _ q).obj
              (((Etale.upperStar (ModuleCat.{u + 1} A) (U i j).ι).mapDerivedCategory).obj K))) ∧
          (∀ q : ℤ, q < r ⟨i, j⟩ ∨ s ⟨i, j⟩ < q →
            IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
              (((Etale.upperStar (ModuleCat.{u + 1} A) (U i j).ι).mapDerivedCategory).obj K))) ∧
          Etale.DerivedCategory.hasTorAmplitudeIn A (U i j).toScheme (a ⟨i, j⟩) (b ⟨i, j⟩)
            (((Etale.upperStar (ModuleCat.{u + 1} A) (U i j).ι).mapDerivedCategory).obj K)) →
        Etale.DerivedCategory.isBoundedConstructible A X K ∧
        (Nonempty X → ∃ rmin smax amin bmax : ℤ,
          IsLeast (Set.range r) rmin ∧ IsGreatest (Set.range s) smax ∧
          IsLeast (Set.range a) amin ∧ IsGreatest (Set.range b) bmax ∧
          (∀ q : ℤ, q < rmin ∨ smax < q →
            IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
          Etale.DerivedCategory.hasTorAmplitudeIn A X amin bmax K) ∧
        (IsEmpty X → IsZero K ∧
          ∀ r₀ s₀ a₀ b₀ : ℤ,
            (∀ q : ℤ, q < r₀ ∨ s₀ < q →
              IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
            Etale.DerivedCategory.hasTorAmplitudeIn A X a₀ b₀ K)) := by
  sorry

end AlgebraicGeometry
