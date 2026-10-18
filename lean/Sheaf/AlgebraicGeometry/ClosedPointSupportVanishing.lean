/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.EtaleSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ClosedPointSheafApproximation
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
import Sheaf.Paper.FiniteCoproductCohomologyAssembly
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.LerayBounded
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
/-!
# Vanishing for abelian étale sheaves supported at closed points

Source: Stacks Project, Tag 0F1F, first assertion; blueprint
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0f1f-vanish.md`
(blueprint: lem-kun-0f1f-vanish).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- An arbitrary abelian étale sheaf supported at closed points of a finite-type scheme
over a separably closed field has zero cohomology in every positive degree.
Source: Stacks Project, Tag 0F1F, first assertion (blueprint: lem-kun-0f1f-vanish).

Proof:
1. A finite-type scheme over a field is Noetherian, hence quasi-compact and quasi-separated
(`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-locally-noetherian-quasi-separated`).
2. By `lem-kun-cp-approximation`, write the sheaf as the set-indexed filtered colimit of
its finitely generated subsheaves, each supported on a finite set of closed points.
The zero subsheaf gives a nonempty index set, and sums give upper bounds. For the reduced
closed immersion on each finite support, `lem-kun-04ca` identifies the subsheaf with the
direct image of its restriction.
3. The reduced finite support is a finite disjoint union of spectra of residue fields:
its singletons are clopen, reduced one-point affine schemes are spectra of fields, and the
surjective stalk maps identify those fields with the residue fields of the ambient scheme
(`def-pc-reduced-scheme`, `def-weil-closed-immersion`, `def-weil-residue-field`).
This includes the empty support and empty coproduct.
4. By `lem-kun-closed-point-field`, those residue fields are separably closed.
`lem-kun-03qu-sep-closed` gives positive-degree vanishing on each component, and
`lem-weil-pbc-finite-coproduct-cohomology-assembly` gives vanishing on the finite support.
The empty product of abelian groups is zero.
5. The closed immersion is finite: on affines it is the quotient map, and the quotient
is generated as a module by one (`def-weil-closed-immersion`,
`def-weil-finite-integral-morphism`).
6. Its direct image is exact by `lemma-weil-pbc-finite-direct-image-exact`.
Apply `lem-kun-leray-bdd` to the sheaves in degree zero and take cohomology as in
`def-weil-pbc-etale-cohomology`; each finite-support subsheaf has zero positive cohomology.
7. By `lem-weil-pbc-cohomology-filtered-colimit`, cohomology on the quasi-compact,
quasi-separated scheme commutes with this filtered colimit, without any torsion hypothesis.
The filtered colimit of the zero groups in positive degree is zero. -/
theorem isZero_cohomology_of_support_subset_closedPoints
    {K : Type u} [Field K] [IsSepClosed K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.etaleSheafSupport F ⊆ closedPoints X) (q : ℕ) (hq : 0 < q) :
    IsZero ((cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
      ((DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) := by
  sorry

end AlgebraicGeometry.Etale
