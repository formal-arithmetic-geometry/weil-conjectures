/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.CompletedAdicIntrinsicCompletion
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Algebra.Homology.Functor
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

/-- Derived evaluation detects isomorphisms by detecting quasi-isomorphisms of complexes.
Source: blueprint order 1253, joint conservativity; Mathlib's levelwise quasi-isomorphism
criterion and essential surjectivity of localization on arrows
(blueprint: lem-weil-pbc-levelwise-isomorphism-cones). -/
private theorem completedAdicEvaluation_jointly_conservative
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M N : DerivedCategory (CompletedAdicTowers T d)) (u : M ⟶ N)
    (hu : ∀ n : ℕ, IsIso ((completedAdicEvaluation T d n).map u)) : IsIso u := by
  classical
  let B := CompletedAdicTowers T d
  have : ((Functor.mapArrowFunctor (CochainComplex B ℤ) (DerivedCategory B)).obj
      (HomotopyCategory.quotient B (.up ℤ) ⋙ DerivedCategory.Qh)).EssSurj := by
    change ((HomotopyCategory.quotient B (.up ℤ)).mapArrow ⋙
      DerivedCategory.Qh.mapArrow).EssSurj
    infer_instance
  have : (DerivedCategory.Q (C := B)).mapArrow.EssSurj :=
    Functor.essSurj_of_iso
      ((Functor.mapArrowFunctor _ _).mapIso (DerivedCategory.quotientCompQhIso B))
  let f := (DerivedCategory.Q (C := B)).mapArrow.objPreimage (Arrow.mk u)
  let e : Arrow.mk (DerivedCategory.Q.map f.hom) ≅ Arrow.mk u :=
    (DerivedCategory.Q (C := B)).mapArrow.objObjPreimageIso (Arrow.mk u)
  have hf : QuasiIso f.hom := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro n
    let F := (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules T d)).obj n
    have h : IsIso (F.mapDerivedCategory.map (DerivedCategory.Q.map f.hom)) :=
      ((MorphismProperty.isomorphisms _).arrow_iso_iff
        ((completedAdicEvaluation T d n.unop).mapArrow.mapIso e)).2 (hu n.unop)
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
      ((NatIso.isIso_map_iff F.mapDerivedCategoryFactors f.hom).1 h)
  exact ((MorphismProperty.isomorphisms _).arrow_iso_iff e).1
    (inferInstanceAs (IsIso (DerivedCategory.Q.map f.hom)))

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
  classical
  let : Zero (DerivedCategory (CompletedAdicTowers T d)) := HasZeroObject.zero' _
  have hcons := completedAdicEvaluation_jointly_conservative T d
  have hunit (C : DerivedCategory (CompletedAdicModules T d))
      (hC : IsCompletedAdicDerivedComplete T d r a ha C) :
      IsIso ((reconstructionCompletionUnit T d).app C) := by
    obtain ⟨j, hj⟩ := reconstructionKoszulIntrinsicComparison T d r a C
    have : IsIso (completedAdicIntrinsicUnit T d r a C) := hC
    have hκ : IsIso ((reconstructionKoszulDerivedUnit T d r a).app C) :=
      IsIso.of_isIso_fac_right hj
    exact (koszulReconstruction T d r a ha).choose_spec.2 C hκ
  refine ⟨?_, ?_, ?_⟩
  · intro M N u hu
    have : IsIso u := hcons M N u hu
    exact ⟨inferInstance, fun RF _ _ ↦ inferInstance⟩
  · intro C hC hred
    have heval (n : ℕ) :
        IsIso ((completedAdicEvaluation T d n).map
          (0 : (0 : DerivedCategory (CompletedAdicTowers T d)) ⟶
            (completedAdicReduction T d).obj C)) := by
      let F := (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules T d)).obj
        (Opposite.op n)
      exact (F.mapDerivedCategory.map_isZero (isZero_zero _)).isIso (hred n) _
    have : IsIso (0 : (0 : DerivedCategory (CompletedAdicTowers T d)) ⟶
        (completedAdicReduction T d).obj C) := hcons _ _ _ heval
    have hz : IsZero ((completedAdicReduction T d).obj C) :=
      (isZero_zero _).of_iso (asIso
        (0 : (0 : DerivedCategory (CompletedAdicTowers T d)) ⟶
          (completedAdicReduction T d).obj C)).symm
    have : IsIso ((reconstructionCompletionUnit T d).app C) := hunit C hC
    exact ((reconstructionLimit T d).isZero_rightDerivedFunctor_obj hz).of_iso
      (asIso ((reconstructionCompletionUnit T d).app C))
  · intro C D u hC hD hu
    have : IsIso ((completedAdicReduction T d).map u) := hcons _ _ _ hu
    have : IsIso ((reconstructionCompletionUnit T d).app C) := hunit C hC
    have : IsIso ((reconstructionCompletionUnit T d).app D) := hunit D hD
    have : IsIso (u ≫ (reconstructionCompletionUnit T d).app D) := by
      change IsIso ((𝟭 _).map u ≫ (reconstructionCompletionUnit T d).app D)
      rw [(reconstructionCompletionUnit T d).naturality u]
      change IsIso ((reconstructionCompletionUnit T d).app C ≫
        (reconstructionRlim T d).map ((completedAdicReduction T d).map u))
      infer_instance
    exact IsIso.of_isIso_comp_right u ((reconstructionCompletionUnit T d).app D)

end AlgebraicGeometry.Scheme
