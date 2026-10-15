/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import Sheaf.AlgebraicGeometry.HypercohomologyFiltrations
import Sheaf.AlgebraicGeometry.TruncationExchangeCouple
import Sheaf.AlgebraicGeometry.FiniteRangeComparison
import Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Bounded allowable-torsion smooth base change

Source: blueprint, sec-smooth-base-change/sk-rem-rest,
sbc-thm-bounded-allowable-torsion (blueprint: sbc-thm-bounded-allowable-torsion).
The ambient conclusion uses the unbounded derived category of abelian sheaves.
The bounded-output clause includes membership and invertibility in the full subcategory.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Smooth base change for bounded allowable-torsion abelian complexes.
Source: blueprint sec-smooth-base-change/sk-rem-rest, bounded allowable-torsion theorem
(blueprint: sbc-thm-bounded-allowable-torsion).

Proof: choose a finite cohomology interval [a,b] for K. Apply
`def-weil-pbc-hypercohomology-filtrations` with the square's roles exchanged to obtain
E2 terms f⁻¹ Rᵖg_* Hᵠ(K) and Rᵖh_* e⁻¹ Hᵠ(K). By
`lem-weil-pbc-truncation-couple-morphism`, the specified exchange induces the morphism
of exact couples, with these degreewise base-change maps on E2.
Each allowable annihilator has only primes invertible on S, hence is invertible on S.
Apply `sbc-thm-smooth-base-change` to each Hᵠ(K); negative higher-image degrees vanish.
Then `sbc-lem-finite-range-comparison` gives isomorphisms on all abutments and of the
specified exchange, without any boundedness assumption on the outputs.
For the last clause, `lem-sbc-qcqs-higher-images-prime-torsion` and
`lemma-openclosed-stalk-upperstar` make the first E2 page allowable-torsion.
Kernels and quotients preserve allowable annihilators. The abutment filtrations are
finite, and `prop-weil-pbc-geometric-stalks-exact` makes their stalks exact filtrations.
In an extension, an annihilator n of the image and an annihilator m of nx multiply
to the allowable annihilator mn of x. Thus the first output has allowable-torsion
cohomology; the ambient isomorphism transfers it to the second. If both are bounded,
both belong to the specified full subcategory. Fullness lifts the exchange and its
inverse with their inverse identities, giving the final isomorphism. -/
theorem isIso_abelianDerivedBaseChangeArrow_of_bounded_allowable_torsion
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (sq : ChosenCartesianSquare h e f g)
    (K : AbelianDerivedCategoryBoundedTorsionOfPrimes T S.invertiblePrimes) :
    IsIso (abelianDerivedBaseChangeArrow sq K.obj) ∧
      (DerivedCategory.TStructure.t.bounded
        (D(upperStar AddCommGrpCat.{u + 1} f).obj
          (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj)) →
       DerivedCategory.TStructure.t.bounded
        (R(lowerStar AddCommGrpCat.{u + 1} h).obj
          (D(upperStar AddCommGrpCat.{u + 1} e).obj K.obj)) →
       ∃ hs : allowableTorsionBoundedProperty X S.invertiblePrimes
          (D(upperStar AddCommGrpCat.{u + 1} f).obj
          (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj)),
       ∃ ht : allowableTorsionBoundedProperty X S.invertiblePrimes
          (R(lowerStar AddCommGrpCat.{u + 1} h).obj
          (D(upperStar AddCommGrpCat.{u + 1} e).obj K.obj)),
       IsIso (ObjectProperty.homMk
         (X := ⟨D(upperStar AddCommGrpCat.{u + 1} f).obj
          (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj), hs⟩)
         (Y := ⟨R(lowerStar AddCommGrpCat.{u + 1} h).obj
          (D(upperStar AddCommGrpCat.{u + 1} e).obj K.obj), ht⟩)
         (abelianDerivedBaseChangeArrow sq K.obj))) := by
  sorry

end AlgebraicGeometry.Etale
