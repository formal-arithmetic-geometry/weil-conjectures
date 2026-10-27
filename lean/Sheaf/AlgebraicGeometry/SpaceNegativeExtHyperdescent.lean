/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.SpaceDerivedSystem
public import Sheaf.AlgebraicGeometry.SpaceFppfHypercover

/-! # Negative Ext hyperdescent for derived quasi-coherent objects

Source: Stacks Project, Simplicial Spaces, Tags 0DLA and 0DL9
(blueprint: lem-sfb-space-negative-ext-hyperdescent).

Coherent systems retain every simplicial operator, including degeneracies. The equalizer
uses the canonical composition comparisons, rather than a freely chosen pair of arrows.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} [∀ A : AlgebraicSpace S, HasDerivedCategory.{w} A.SmallModules]

/-- Object hyperdescent, morphism hyperdescent, negative cross-Ext vanishing, and
conservative pullback for unbounded quasi-coherent complexes on an fppf space hypercover.
Source: Stacks, Simplicial Spaces, Tags 0DLA and 0DL9
(blueprint: lem-sfb-space-negative-ext-hyperdescent).

Proof:
1. Restrict the given system to injective order maps. By
lem-sfb-hypercover-augmentation-face-property all face and augmentation pullbacks are
exact. Form the face ringed total category of lem-sfb-semisimplicial-ringed-total-category,
using the enlarged étale sites of lem-sfb-fppf-face-total-qcoh-equivalence.
2. The negative self-Hom condition permits lem-sfb-flat-semisimplicial-derived-realization
to realize the system on this total category. Its quasi-coherent cartesian cohomology
places it in the subcategory equivalent to D_QCoh(X), by
lem-sfb-fppf-face-total-qcoh-equivalence. Apply its inverse and evaluate to obtain the
required objects and face-compatible isomorphisms. A degeneracy has a face retraction;
pull face compatibility along it and use the given system's composition law. This proves
compatibility with degeneracies, hence with every simplicial map.
3. For M,N use the same equivalence and lem-sfb-flat-semisimplicial-derived-hom to identify
Hom with compatible component maps. Every compatible family is determined by degree
zero. Conversely pull a degree-zero map along a vertex; its two restrictions agreeing
in degree one implies, by pulling along all edges, independence of the vertex. These
maps commute with all injective operators. This proves injectivity and the exact image
condition displayed below.
4. For i<0 apply this injectivity to M,N[i]. The shifted negative cross-Hom hypotheses
hold since i+t<0 for t<0; the degree-zero restriction of every such map is zero.
5. Exact component evaluations detect zero cohomology on the face total category.
The total equivalence therefore detects zero objects on X. Applying this to the cone
of an arrow detects isomorphisms, since derived pullback is triangulated. Detection
uses no negative Ext assumption. No degeneracy is assumed flat in this argument. -/
theorem space_negative_ext_hyperdescent {X : AlgebraicSpace S}
    (U : SimplicialObject (Over X)) (hU : IsSpaceFppfHypercover U) :
    (∀ D : SpaceDerivedSystem U,
      (∀ (n : ℕ) (i : ℤ), i < 0 →
        Subsingleton (D.obj (SimplexCategory.mk n) ⟶
          (D.obj (SimplexCategory.mk n))⟦i⟧)) →
      ∃ K : X.DerivedModules, X.derivedQCohProperty K ∧
        ∃ e : ∀ n : SimplexCategory,
          (spaceDerivedPullback (U.obj (op n)).hom).obj K ≅ D.obj n,
          ∀ (m n : SimplexCategory) (φ : m ⟶ n),
            (e n).hom = (spaceAugmentationComparison U φ).hom.app K ≫
              (spaceDerivedPullback (U.map φ.op).left).map (e m).hom ≫
              (D.transition φ).hom) ∧
    (∀ M N : X.DerivedModules,
      X.derivedQCohProperty M → X.derivedQCohProperty N →
      (∀ (n : ℕ) (i : ℤ), i < 0 →
        Subsingleton ((spaceDerivedPullback (U.obj (op (SimplexCategory.mk n))).hom).obj M ⟶
          ((spaceDerivedPullback (U.obj (op (SimplexCategory.mk n))).hom).obj N)⟦i⟧)) →
      Function.Injective
          ((spaceDerivedPullback (U.obj (op (SimplexCategory.mk 0))).hom).map
            (X := M) (Y := N)) ∧
        (∀ a : (spaceDerivedPullback (U.obj (op (SimplexCategory.mk 0))).hom).obj M ⟶
            (spaceDerivedPullback (U.obj (op (SimplexCategory.mk 0))).hom).obj N,
          spaceDegreeOneRestriction U a 0 = spaceDegreeOneRestriction U a 1 ↔
            ∃ b : M ⟶ N,
              (spaceDerivedPullback (U.obj (op (SimplexCategory.mk 0))).hom).map b = a) ∧
        (∀ i : ℤ, i < 0 → Subsingleton (M ⟶ N⟦i⟧))) ∧
    (∀ K : X.DerivedModules, X.derivedQCohProperty K →
      (∀ n : ℕ,
        IsZero ((spaceDerivedPullback (U.obj (op (SimplexCategory.mk n))).hom).obj K)) →
      IsZero K) ∧
    (∀ K L : X.DerivedModules,
      X.derivedQCohProperty K → X.derivedQCohProperty L →
      ∀ f : K ⟶ L, (∀ n : ℕ,
        IsIso ((spaceDerivedPullback (U.obj (op (SimplexCategory.mk n))).hom).map f)) →
      IsIso f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
