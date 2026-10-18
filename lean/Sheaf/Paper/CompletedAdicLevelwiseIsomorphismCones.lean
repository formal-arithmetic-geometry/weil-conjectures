/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.CompletedAdicIntrinsicCompletion
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Sheaf.Algebra.Homology.KFlatClosure
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.KoszulReconstruction

/-! # Levelwise isomorphisms and complete cones

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1253;
Stacks Tags 099M, 099Q and 099P
(blueprint: lem-weil-pbc-levelwise-isomorphism-cones).

The Rlim clause ranges over its universal total-right-derived-functor realizations.
The comparison with ordinary inverse limit is part of that universal pair: it does not
quantify over arbitrary endofunctors or replace the specified derived limit by a choice
of unnormalized cone maps. Its existence and Roos-triangle computation belong to
prop-weil-pbc-rlim-functoriality. All coefficient objects are A_T-module objects.
-/

@[expose] public section

set_option autoImplicit false

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Joint conservativity of derived evaluations, its preservation by Rlim, and finite
reduction conservativity on the derived complete subcategory.
Source: blueprint order 1253; Stacks Tags 099M, 099Q and 099P
(blueprint: lem-weil-pbc-levelwise-isomorphism-cones).

Proof:
1. Complete a tower map u to a distinguished triangle with cone E. The exact evaluations
are triangulated (lem-sf-exact-functor-derived-triangulated). Comparison with the identity
triangle and lem-sf-triangle-morphism-iso show that every evaluation of E is zero.
Cohomology of towers is levelwise (def-weil-pbc-adic-coefficient-datum), so all cohomology
of E vanishes. Its representing complex is acyclic, and derived localization
(def-weil-abstract-derived-category) makes E zero. Comparing triangles again makes u an
isomorphism.
2. A realization of Rlim supplied by prop-weil-pbc-rlim-functoriality is a functor, so it
sends the inverse of u to the inverse of its image. Its universal comparison to ordinary
inverse limit identifies it with the specified sequential derived inverse limit.
3. The quotient-reduction tower functor preserves triangles. Compute on K-flat cone
models using lem-pc-kflat-resolution and lem-pc-kflat-cone-direct-sum. The cone-tensor
isomorphisms commute with every quotient transition on both summands. Change of K-flat
representative gives quasi-isomorphisms levelwise by lem-pur-derived-change-of-rings,
hence in the tower category by step 1. Thus the strict cone calculation descends to the
derived tower category. Applying the triangulated Rlim functor proves exactness of the
completion. Its units form a morphism of triangles, since x maps to x tensor 1 in both
cone summands, including the shifted last square.
4. For complete C, prop-weil-pbc-koszul-reconstruction identifies C with Rlim of its
quotient tower. If all reductions vanish, step 1 makes that tower zero. Additivity of
Rlim makes its image zero, so C is zero.
5. For a map of complete objects, its cone E is complete: the completion units give a
map of distinguished triangles with the first two components invertible. The triangle
isomorphism lemma makes the third invertible. The unit-compatible Koszul reconstruction
comparison identifies this with the intrinsic Koszul unit of E, so E is complete.
6. If all reductions of the map are isomorphisms, exactness of reduction and comparison
with the identity triangle make every reduction of E zero. Steps 4 and 5 give E zero;
comparison of the original triangle with the identity triangle then makes the map an
isomorphism. No constant-coefficient/completed-coefficient equivalence is used. -/
theorem completedAdic_levelwise_isomorphism_cones
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    (∀ (M N : DerivedCategory (CompletedAdicTowers T d)) (u : M ⟶ N),
      (∀ n : ℕ, IsIso ((completedAdicEvaluation T d n).map u)) →
      IsIso u ∧
        ∀ (RF : DerivedCategory (CompletedAdicTowers T d) ⥤
            DerivedCategory (CompletedAdicModules T d))
          (η : (lim : CompletedAdicTowers T d ⥤ CompletedAdicModules T d).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF),
          RF.IsRightDerivedFunctor η
              (HomologicalComplex.quasiIso (CompletedAdicTowers T d) (ComplexShape.up ℤ)) →
            IsIso (RF.map u)) ∧
    (∀ C : DerivedCategory (CompletedAdicModules T d),
      IsCompletedAdicDerivedComplete T d r a ha C →
      (∀ n : ℕ, IsZero ((completedAdicFiniteReduction T d n).obj C)) → IsZero C) ∧
    (∀ (C D : DerivedCategory (CompletedAdicModules T d)) (u : C ⟶ D),
      IsCompletedAdicDerivedComplete T d r a ha C →
      IsCompletedAdicDerivedComplete T d r a ha D →
      (∀ n : ℕ, IsIso ((completedAdicFiniteReduction T d n).map u)) → IsIso u) := by
  sorry

end AlgebraicGeometry.Scheme
