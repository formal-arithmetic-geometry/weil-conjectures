/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfDerivedComplete
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.IntegralReductionTowerWellDefined
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Paper.CompletedIntegralCoefficientGerm
import Sheaf.Paper.IntegralReductionTower
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Paper.DerivedCompleteUnrestricted
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.IntegralReductionTowerCanonical
import Sheaf.Paper.ProEtaleConstructibleSheaf
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle

/-!
# Triangulation of the intrinsic integral constructible category

Source: Bhatt--Scholze, Section 6.5, after Definition 6.5.1, for the uniform-reduction
variant in blueprint order 1459; Stacks Project, Tag 0999
(blueprint: lem-weil-integral-constructible-triangulated).

The predicate is the recorded `sfIntegralConstructible`, over the completed coefficient
sheaf on the small pro-etale site. The two instances below make Mathlib's inherited
shift, pretriangulation, triangulation and exact full-subcategory inclusion available
on `sfIntegralConstructibleCategory`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

/-- The intrinsic integral constructible predicate is closed under isomorphisms.
Source: Bhatt--Scholze, Section 6.5, after Definition 6.5.1; blueprint order 1459
(blueprint: lem-weil-integral-constructible-triangulated).

Proof: an isomorphism induces isomorphisms of all reductions and intertwines their
canonical units and transitions. Transport a product witness and its distinguished
Roos triangle to obtain derived completeness of the isomorphic object. At every
positive level, cohomology sheaves are isomorphic, preserving finite-torsion
constructibility and the same uniform cohomological interval. These are precisely
the defining clauses of `sfIntegralConstructible` (proof steps 2 and 5 of the node).
-/
@[instance]
theorem sfIntegralConstructible_isClosedUnderIsomorphisms
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (sfIntegralConstructible l E Y) := by
  sorry

/-- Derived-complete integral objects whose constructible reductions have a common
finite cohomological interval form a triangulated object property. Together with
isomorphism closure above, this states zero, integer-shift and extension closure
for the actual predicate. Mathlib's full-subcategory construction supplies the
inherited distinguished triangles and makes the inclusion exact.
Source: Bhatt--Scholze, Section 6.5, after Definition 6.5.1, for the variant of
blueprint order 1459; Stacks Project, Tag 0999
(blueprint: lem-weil-integral-constructible-triangulated).

Proof:
1. Write B for the completed integral coefficient sheaf and B_n for the finite
constant quotient sheaves (`def-weil-completed-integral-coefficients` and
`def-weil-integral-reduction-tower`). Quotient completion C(M), with its canonical
unit, agrees with one-generator Koszul completion by
`lem-weil-pbc-constant-completion-equivalence`. The coefficient valuation ring is
Noetherian, and its uniformizer generates the ideal. Thus
`lem-weil-pbc-ringed-koszul-completion-reflector` makes C(M) locally complete and
identifies invertibility of the unit with local completeness, on an arbitrary Y.
2. This local condition agrees with `def-weil-derived-complete`, as used by
`IsSfDerivedComplete`. Exact countable
products (`lem-weil-proetale-countable-products-exact`) and
`lem-weil-derived-limit-existence` identify the products in the K-injective tower
with the original reduction products. Apply
`lem-weil-derived-limit-tower-core-property-triangle` to obtain the Roos triangle
on C(M); the composite of its first arrow with the unit has the canonical quotient
components. An invertible unit transports this triangle to the required triangle
on M. Conversely rotate the two Roos triangles to their common first arrow 1-s;
TR3 and `lem-sf-triangle-morphism-iso` give M isomorphic to C(M). Local completeness
is invariant under this isomorphism, so the unit is invertible by step 1. The ringed
module and diagram Grothendieck results (`lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-weil-pbc-small-module-diagrams-grothendieck`), together with
`lem-sp-grothendieck-enough-injectives` and
`lem-weil-pbc-kinjective-functorial-existence`, supply the injective resolutions.
No uniqueness of an arbitrary lift to a homotopy limit is asserted.
3. Local completeness is equivalent to vanishing of RHom_B(B[1/t],M), with t the
uniformizer: restriction of internal Hom gives the condition on every slice, and
`lem-weil-pbc-ringed-derived-complete-elements-ideal` extends it from the generator
to all local ideal sections. By
`lem-weil-pbc-ringed-internal-hom-exact-restriction`, this internal-Hom functor is
exact and commutes with shifts. It preserves zero and isomorphisms. Applied to a
triangle with complete outside vertices it has zero outside vertices; the long
exact cohomology sequence (`lem-sf-derived-homology-long-exact`) kills the middle.
Thus completeness is closed under zero, isomorphisms, shifts and extensions.
4. At each positive exponent the reduction functor
(`def-weil-integral-derived-reduction`, `scalarReductionDerivedExtension`)
is exact triangulated by
`lem-pur-derived-change-of-rings` applied to the identity site and B to B_n.
It preserves zero, isomorphisms, shifts and distinguished triangles. Flatness of
B_n over B is not required for a derived functor.
5. The zero object's reductions have empty support, in [0,0]. Isomorphisms
preserve cohomology and constructibility. For a shift by m,
`lem-sp-derived-cohomology-shift` translates a uniform interval [r,s] to
[r-m,s-m]. `lem-weil-proetale-dbc-triangulated` supplies finite-level zero,
isomorphism and shift closure. Its constructibility agrees with
`def-weil-finite-torsion-constructibility` and
`def-weil-proetale-constructible-sheaf`: finite locally closed constructible
partitions, locally constant restrictions with finite stalks, and bounded
cohomology. Combine this with step 3 and
`def-weil-derived-complete-integral-detailed` for the integral closure assertions.
6. Reduce a distinguished triangle with integral constructible outside vertices.
Each coefficient quotient is finite. Thus
`lem-weil-proetale-dbc-triangulated` gives bounded constructibility of the middle
reduction at every level, and step 3 gives completeness of the middle object.
7. If the outside uniform intervals are [r',s'] and [r'',s''], use
[min(r',r''),max(s',s'')]. Outside this interval the exact cohomology segment has
zero outside terms, hence zero middle term, by
`lem-sf-derived-homology-long-exact`. This proves the common support bound of
`def-weil-cohomological-support`, independently of the reduction level. No common
stratification or rank bound across levels is required.
8. The category is full by definition. The preceding closure properties make its
object property triangulated and isomorphism-closed. Cone closure follows by
rotation and shifts. `def-weil-triangulated-subcategory` supplies the inherited
triangulated structure and exact inclusion. -/
@[instance]
theorem sfIntegralConstructible_isTriangulated
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty.IsTriangulated (sfIntegralConstructible l E Y) := by
  sorry

end WeilConjectures
