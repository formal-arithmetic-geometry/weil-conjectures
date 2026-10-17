/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ConstructibleOfFiniteDirectImage
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes

/-!
# Finite direct image reflects bounded constructibility

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-reflects-derived.md
(blueprint: lem-fin-finite-reflects-derived).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- For a finite morphism of Noetherian schemes and a finite commutative coefficient ring,
the total derived direct image on ordinary, unbounded etale module derived categories
reflects membership in `D^b_c`.

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-reflects-derived.md
(blueprint: lem-fin-finite-reflects-derived).

Proof plan:
1. Finite direct image is exact on abelian sheaves
(`lemma-weil-pbc-finite-direct-image-exact`), and hence on module sheaves, because the
underlying abelian sheaves compute kernels and sheafified cokernels
(`def-weil-sheaf-of-modules-category`). Apply
`lem-weil-pbc-exact-functor-derived-factorization` and
`lem-weil-pbc-exact-functor-derived-functor`: even an unbounded complex computes the
right derived functor. By `lem-weil-pbc-exact-functor-complex-cohomology`, its degree-q
cohomology is the direct image of the degree-q cohomology of the original complex.
2. If the direct image of a module sheaf vanishes, the finite stalk formula
(`lemma-weil-pbc-finite-stalk-formula`) makes every geometric stalk vanish: each stalk
is a factor in a zero product, and each factor embeds by inserting zero in the other
coordinates. Geometric stalk conservativity
(`lemma-weil-pbc-geometric-stalk-conservative`) then makes the sheaf zero. Apply this
in every degree outside the bounded interval of the image; the same interval bounds K.
3. In every remaining degree apply `lem-fin-finite-reflects-constructibility` to the
cohomology sheaf, using the cohomology comparison from step 1. Outside the interval the
zero sheaf is finite locally constant and constructible (one stratum for a nonempty
scheme, the empty partition for the empty scheme). The recorded definition
`def-weil-pbc-constructible-complexes` now gives bounded constructibility of K. -/
theorem isBoundedConstructible_of_finite_rightDerivedLowerStar
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Z S : Scheme.{u}} [IsNoetherian Z] [IsNoetherian S]
    (p : Z ⟶ S) [IsFinite p] (K : DerivedCategoryModule Λ Z)
    (hK : DerivedCategory.isBoundedConstructible Λ S
      ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) p).obj K)) :
    DerivedCategory.isBoundedConstructible Λ Z K := by
  sorry

end AlgebraicGeometry.Etale
