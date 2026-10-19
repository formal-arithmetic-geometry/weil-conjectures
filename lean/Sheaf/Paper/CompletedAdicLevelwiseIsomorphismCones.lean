/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.CompletedAdicIntrinsicCompletion
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
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
  have tower_iso : ∀ (M N : DerivedCategory (CompletedAdicTowers T d)) (u : M ⟶ N),
      (∀ n, IsIso ((completedAdicEvaluation T d n).map u)) → IsIso u := by
    intro M N u hu
    let C := CompletedAdicTowers T d
    let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
    have := Localization.essSurj_mapArrow (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    let g := (DerivedCategory.Qh (C := C)).mapArrow.objPreimage (Arrow.mk u)
    let f := q.mapArrow.objPreimage g
    let e : Arrow.mk (DerivedCategory.Q.map f.hom) ≅ Arrow.mk u :=
      (((Functor.mapArrowFunctor _ _).mapIso (DerivedCategory.quotientCompQhIso C)).app f).symm ≪≫
        DerivedCategory.Qh.mapArrow.mapIso (q.mapArrow.objObjPreimageIso g) ≪≫
        DerivedCategory.Qh.mapArrow.objObjPreimageIso (Arrow.mk u)
    apply ((MorphismProperty.isomorphisms _).arrow_iso_iff e).1
    change IsIso (DerivedCategory.Q.map f.hom)
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro n
    let E := (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules T d)).obj n
    have h : IsIso (E.mapDerivedCategory.map (DerivedCategory.Q.map f.hom)) := by
      have hn := hu n.unop
      exact ((MorphismProperty.isomorphisms _).arrow_iso_iff
        (E.mapDerivedCategory.mapArrow.mapIso e)).2 hn
    have h' := (NatIso.isIso_map_iff E.mapDerivedCategoryFactors f.hom).1 h
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 h'
  have tower_zero : ∀ M : DerivedCategory (CompletedAdicTowers T d),
      (∀ n, IsZero ((completedAdicEvaluation T d n).obj M)) → IsZero M := by
    intro M hM
    apply ((isIsoZero_iff_source_target_isZero M M).1 ?_).1
    apply tower_iso M M 0
    intro n
    change IsIso (((CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules T d)).obj
      (Opposite.op n)).mapDerivedCategory.map 0)
    rw [Functor.map_zero]
    exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨hM n, hM n⟩
  have complete_unit : ∀ K : DerivedCategory (CompletedAdicModules T d),
      IsCompletedAdicDerivedComplete T d r a ha K →
        IsIso ((reconstructionCompletionUnit T d).app K) := by
    intro K hK
    rcases reconstructionKoszulIntrinsicComparison T d r a K with ⟨j, hj⟩
    have hcomp : IsIso ((reconstructionKoszulDerivedUnit T d r a).app K ≫ j.hom) := by
      rw [hj]
      exact hK
    have hκ : IsIso ((reconstructionKoszulDerivedUnit T d r a).app K) :=
      IsIso.of_isIso_comp_right _ j.hom
    rcases koszulReconstruction T d r a ha with ⟨c, _, hc⟩
    exact hc K hκ
  refine ⟨?_, ?_, ?_⟩
  · intro M N u hu
    have h := tower_iso M N u hu
    exact ⟨h, fun RF _ _ ↦ RF.map_isIso u⟩
  · intro C hC hred
    have hzero : IsZero ((completedAdicReduction T d).obj C) :=
      tower_zero _ hred
    have hunit := complete_unit C hC
    exact ((reconstructionRlim T d).map_isZero hzero).of_iso
      (asIso ((reconstructionCompletionUnit T d).app C))
  · intro C D u hC hD hu
    have hred := tower_iso _ _ ((completedAdicReduction T d).map u) hu
    have hCunit := complete_unit C hC
    have hDunit := complete_unit D hD
    have hcomp : IsIso (u ≫ (reconstructionCompletionUnit T d).app D) := by
      change IsIso ((𝟭 _).map u ≫ (reconstructionCompletionUnit T d).app D)
      rw [(reconstructionCompletionUnit T d).naturality u]
      change IsIso ((reconstructionCompletionUnit T d).app C ≫
        (reconstructionRlim T d).map ((completedAdicReduction T d).map u))
      infer_instance
    exact IsIso.of_isIso_comp_right u ((reconstructionCompletionUnit T d).app D)

end AlgebraicGeometry.Scheme
