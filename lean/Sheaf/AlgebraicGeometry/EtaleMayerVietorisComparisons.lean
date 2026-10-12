module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Cohomology on Sites, Tag 03F3 (2).
(blueprint: lem-weil-pbc-etale-mayer-vietoris-comparisons)

Proof: Choose a bounded below injective resolution of a sheaf on X's small etale site.
Evaluation at each of X, U, V and U ∩ V computes its right derived evaluation functor.
For an open immersion, inverse image is restriction to the localized site and preserves
injectives: extension by zero is its exact left adjoint. Thus restriction of the resolution
is an injective resolution on that open. Global sections of the restricted resolution
are naturally the sections of the original resolution on the corresponding etale object.
Taking homology identifies right derived evaluation with derived global sections of the
restricted sheaf in degree zero. At X use the same resolution without restriction.
Comparison maps between resolutions are unique up to homotopy, so these identifications
are natural in the sheaf and give the four functor isomorphisms, independently in every
nonnegative degree. No covering assumption is needed. -/
theorem etale_mayerVietoris_comparisons (X : Scheme.{u}) (U V : X.Opens) :
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerived n ≅
      (DerivedCategory.singleFunctor _ 0 ⋙ cohomology AddCommGrpCat.{u + 1} X n)) ∧
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk U.ι))).rightDerived n ≅
      (upperStar AddCommGrpCat.{u + 1} U.ι ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} U.toScheme n)) ∧
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk V.ι))).rightDerived n ≅
      (upperStar AddCommGrpCat.{u + 1} V.ι ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} V.toScheme n)) ∧
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (U ⊓ V).ι))).rightDerived n ≅
      (upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} (U ⊓ V).toScheme n)) := by
  sorry

end AlgebraicGeometry.Etale
