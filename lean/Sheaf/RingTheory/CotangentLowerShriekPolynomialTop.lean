/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.RingTheory.PolynomialPresentationPairCategories
public import Sheaf.CategoryTheory.DerivedColimitBar
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.RingTheory.CotangentResolutionCoherence
import Sheaf.AlgebraicTopology.SurjectiveQuasiIsoTrivialKan
import Sheaf.Paper.TrivialKanHomotopyEquivalence

/-!
# Evaluation of the presentation-pair derived colimit at a polynomial target

Source: Stacks Project, Cotangent Complex, Tag 08QV (lemma-polynomial-on-top),
with module coefficients as in Cohomology on Sites, Tag 08Q9
(blueprint: lem-trf-cotangent-lower-shriek-polynomial-top).

Both sites have the bottom topology, so coefficients are ordinary module presheaves.
`CategoryColimitBarSystem` supplies the canonical models and reindexing maps. The
augmentation maps below are specified on every bar generator and in every degree;
they are consequently canonical, rather than unspecified maps to an isomorphic object.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Algebra.PolynomialPresentation

/-- The complete generator specification of an augmentation from a category bar complex
into a module in degree zero. Source: Stacks 08PG, 08PH and 08QV
(blueprint: lem-trf-cotangent-lower-shriek-polynomial-top). -/
def IsEvaluationAugmentation {D : Type u} [SmallCategory D]
    {R : Type u} [CommRing R] (model : CategoryColimitBarModel D R)
    (F : Dᵒᵖ ⥤ ModuleCat.{u} R) (M : ModuleCat.{u} R)
    (restrictions : ∀ T : D, F.obj (op T) ⟶ M)
    (ε : model.bar.obj F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) : Prop :=
  (∀ c : ComposableArrows D 0,
    model.generator F 0 c ≫ ε.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom = restrictions c.right) ∧
  (∀ r : ℤ, r ≠ 0 → ε.f r = 0)

/-- For C = B[E], the canonical evaluation augmentation on presentation pairs is an
isomorphism in D(R), and factors through the canonical reindexing to polynomial
B-algebras and their evaluation augmentation. The cardinal bound is infinite and contains
A and B; E and all variable sets are its subsets. Every set of generators in the chosen
bound has such a representative. The two existential chain maps are uniquely specified
by `IsEvaluationAugmentation`, not arbitrary maps.

Source: Stacks 08QV (lemma-polynomial-on-top), module coefficients via 08Q9
(blueprint: lem-trf-cotangent-lower-shriek-polynomial-top).

Proof:
1. Regard presheaves on the opposite sites as covariant functors on the ordinary
   presentation categories. Use [lem-trf-derived-colimit-bar]. Identify its last-vertex
   bar convention with the first-vertex convention of
   [lem-trf-simplicial-derived-colimit-computation] by multiplication in degree -n by
   (-1)^(n(n+1)/2). This is identity in degree zero and respects reindexing and augmentation.
   Take the standard polynomial resolution P of B/A from
   [lem-trf-cotangent-resolution-coherence], and use the simplicial pairs (P_n,P_n[E]).
2. The resolution is termwise surjective and its alternating complex resolves B.
   The alternating complex of the constant B has differential zero in odd positive chain
   degrees and identity in even positive degrees. Therefore P → const B is a quasi-isomorphism.
   Apply [lem-trf-surjective-qis-simplicial-group-trivial-kan] to obtain a trivial Kan fibration.
3. Coefficients in monomials identify P[E] → const B[E] with a direct sum of copies of
   P → const B. Cycles have finite support, so homology commutes with this direct sum.
   Lift the finitely many coefficients to obtain termwise surjectivity. The same criterion
   gives a trivial Kan fibration, also for infinite E.
4. For a pair A[S], A[S][T], maps to the simplicial pairs are freely specified by one
   lift for every s in S and t in T. The trivial Kan lifting properties of steps 2 and 3
   fill every boundary coordinatewise, including vertices. Empty products are singletons.
   [def-weil-pbc-trivial-kan-fibration] and
   [lem-weil-pbc-trivial-kan-homotopy-equivalence] give representable contractibility.
5. Apply [lem-trf-simplicial-derived-colimit-computation]. Base change sends the chosen
   simplicial pairs to the constant identity-augmented C, fixing coefficients and variables.
   Naturality of that computation identifies the two comparison maps and proves that
   reindexing is an isomorphism in D(R).
6. The identity-augmented C is terminal before taking opposites. Its constant resolution
   computes the target bar complex. Reindexing from the one-object category identifies its
   evaluation augmentation with the constant-complex augmentation. The latter is contracted
   by the identity in odd positive chain degrees and zero in even degrees, so is a
   quasi-isomorphism, for every module, including zero.
7. On a degree-zero bar generator, the composite reindexes the pair then restricts along
   C → Q ⊗_P B in the opposite category. In all other degrees it is zero. Thus it is exactly
   the displayed augmentation, with the required factorization, and its derived map is an
   isomorphism as the composite of the isomorphisms of steps 5 and 6. -/
theorem polynomial_top_evaluation (I A B R : Type u) [Infinite I]
    [CommRing A] [CommRing B] [Algebra A B] [CommRing R]
    (_boundA : Nonempty (A ↪ I)) (_boundB : Nonempty (B ↪ I)) (E : Set I)
    (system : CategoryColimitBarSystem.{u})
    (F : (Target I B E)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R) :
    ∃ (εD : (system.models (Target I B E)ᵒᵖ R).bar.obj F ⟶
        (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
          (F.obj (op (op (topTarget I B E)))))
      (εP : (system.models (Pair I A B E)ᵒᵖ R).bar.obj
          ((baseChange I A B E).op.op ⋙ F) ⟶
        (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
          (F.obj (op (op (topTarget I B E))))),
      IsEvaluationAugmentation (system.models (Target I B E)ᵒᵖ R) F
        (F.obj (op (op (topTarget I B E))))
        (fun T ↦ F.map (toTop I B E T.unop).op.op) εD ∧
      IsEvaluationAugmentation (system.models (Pair I A B E)ᵒᵖ R)
        ((baseChange I A B E).op.op ⋙ F) (F.obj (op (op (topTarget I B E))))
        (fun W ↦ F.map (toTop I B E W.unop.target).op.op) εP ∧
      εP = system.map (baseChange I A B E).op (RingHom.id R)
        (𝟙 ((baseChange I A B E).op.op ⋙ F)) ≫ εD ∧
      IsIso (DerivedCategory.Q.map εP) := by
  sorry

end Algebra.PolynomialPresentation
