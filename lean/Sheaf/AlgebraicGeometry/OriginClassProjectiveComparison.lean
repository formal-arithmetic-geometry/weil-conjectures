/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module
public import Sheaf.AlgebraicGeometry.OriginComparisonArrows
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.DerivedDirectImageComposition
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import Sheaf.AlgebraicGeometry.GeometricPointCohomology

/-!
# The affine origin and the positive projective Chern class

Source: main-20261015 sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Step 2; master sk-prop-an, Step 5(d).
(blueprint: lem-pur-origin-class-projective-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.AffineSpace

/-- The exact witnesses and clauses of the origin comparison. The record adds no
choices beyond the boundary, canonical restriction, positive Chern and section-one
normalizations displayed in its fields.
Source: blueprint rank-one Thom, Step 2
(blueprint: lem-pur-origin-class-projective-comparison). -/
structure OriginProjectiveComparison (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) where
  hX : IsUnit (N : Γ(AffineSpace PUnit.{u + 1} S, ⊤))
  hP : IsUnit (N : Γ(ProjectiveLine S, ⊤))
  hIX : (AffineSpace.zeroSection PUnit.{u + 1} S).ker.IsInvertible
  hIP : (ProjectiveLine.infinity S).ker.IsInvertible
  transport : OrdinaryFiniteTwistTransport A N hA
  restriction : (upperStar (ModuleCat.{u + 1} A) (ProjectiveLine.infinityChart S)).obj
    (originProjectiveSheaf A S) ≅ originAffineSheaf A S
  affineClass : Ext (originAffineSheaf A S)
    (Scheme.finiteEtaleTateLine (AffineSpace PUnit.{u + 1} S) N A hA) 2
  projectiveClass : Ext (originProjectiveSheaf A S)
    (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2
  chern : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
    (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  sourceIso : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj (ModuleCat.of A A) ≅
    (originCompactSections A S).obj
      ((DerivedCategory.singleFunctor _ 0).obj (originAffineSheaf A S))
  restriction_normalization : restriction.hom = originRestrictionExchange A S
  affine_boundary : SupportedKummerBoundary A N hA
    (AffineSpace.zeroSection PUnit.{u + 1} S) hIX hX affineClass
  projective_boundary : SupportedKummerBoundary A N hA
    (ProjectiveLine.infinity S) hIP hP projectiveClass
  divisor_iso : Nonempty (Scheme.Modules.dual (ProjectiveLine.infinity S).ker.toModules ≅
    ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)
  divisor_transition : Nonempty (ProjectiveLine.TwistData S 1
    (Scheme.Modules.dual (ProjectiveLine.infinity S).ker.toModules))
  chern_normalization : ordinaryFiniteP1ChernSpec A N hA S hP chern
  equations : originComparisonEquations (originOpenExtension A S)
    (originSections A (ProjectiveLine S))
    (originBoundaryArrow A N hA (AffineSpace PUnit.{u + 1} S) _ affineClass)
    (originBoundaryArrow A N hA (ProjectiveLine S) _ projectiveClass)
    (originSupportCounit A S restriction) (originTwistCounit A N hA transport S hP)
    ((DerivedCategory.singleFunctor _ 0).map
      (supportedConstantUnit A (ProjectiveLine.infinity S))) chern
    (originConstantSectionsUnit A (ProjectiveLine S)) sourceIso

/-- The supported affine-origin class has compact image equal to the positive O(1) Chern class.
Source: main-20261015 sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2; master sk-prop-an, Step 5(d).
(blueprint: lem-pur-origin-class-projective-comparison).

Proof:
1. The ideal of [1:0] has frames t and 1 on D(x₀), D(x₁). Dualizing gives
   g₀=t⁻¹g₁ and O(D₀)=O(1); the canonical section is x₁ with coordinates t,1
   (def-pc-divisor-line-bundle, def-pc-projective-space-twist).
2. The direct-image formula gives the canonical restriction exchange. The supported
   sheaf vanishes on D(x₁), so the open/closed exact sequence makes e invertible
   (lem-weil-pbc-open-closed-short-exact).
3. Localize the exact original open adjunction, retaining its actual counit
   (lem-weil-pbc-extension-by-zero-adjunction, lem-weil-pbc-extension-by-zero-exact,
   prop-weil-pbc-inverse-image-modules-exact, def-weil-exact-derived-adjunction).
4. Pullback compatibility of ordinary_supported_kummer identifies the boundary classes.
   Naturality of this actual counit yields the equality of arrows, without inferring
   a derived equality from equality only after restriction
   (lem-asd-ordinary-supported-kummer, lem-asd-etale-finite-twist-pullback).
5. Closed direct image is finite and exact. Derived composition, forgetting module
   cohomology and geometric point cohomology identify RΓ(P,F) with A[0], sending 1 to 1.
   With e this gives lambda with the displayed closed-unit normalization
   (lem-weil-pbc-closed-immersion-finite, lemma-weil-pbc-finite-direct-image-exact,
   def-weil-pbc-derived-direct-image-composition, lem-weil-pbc-etale-module-cohomology-forget,
   lem-weil-pbc-geometric-point-cohomology, def-amb-etale-compact-support).
6. Apply RΓ to Step 4 and precompose with lambda. Forgetting support gives the
   ordinary Kummer Chern class of O(D₀)=O(1). Thus a tau = h with coefficient +1.
   Supported and compact cohomology were never assumed identified.
-/
theorem origin_class_projective_comparison (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (N : ℕ) (hN : 0 < N) (hΩ : IsUnit (N : Ω))
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    Nonempty (OriginProjectiveComparison A N hA (Spec (.of Ω))) := by
  sorry

end AlgebraicGeometry.Etale
