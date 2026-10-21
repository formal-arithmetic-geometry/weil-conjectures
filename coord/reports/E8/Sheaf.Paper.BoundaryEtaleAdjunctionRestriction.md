## What changed

Filled `AlgebraicGeometry.Etale.boundary_etale_adjunction_restriction` in
`Sheaf.Paper.BoundaryEtaleAdjunctionRestriction`. Both public proposition definitions and the
entire theorem signature are unchanged. No other Lean module is changed.

The proof constructs the geometric assertions using the existing Noetherianity instances,
Nagata compactification, and the finite-dimensionality theorem. For each compactification,
the algebraic-closure datum gives the required separably closed base, and the stated torsion
direct-image dimension bound gives classical vanishing above `2*d`, via
`homologyRightDerivedFunctorPlusObjSingleFunctorIso`. The stated unbounded upper-amplitude
theorem then gives `F_c(D^{≤m}) ⊆ D^{≤m+2*d}`. Adjunction orthogonality proves the corresponding
lower bound `R_c(D^{≥b}) ⊆ D^{≥b-2*d}` directly for this compactification. This establishes
boundedness before any adjunction restriction.

The existing plus compatibility isomorphism proves boundedness of `F_c` immediately. The
right functor is lifted to the full subcategory, and the restricted adjunction is exactly
`Adjunction.restrictFullyFaithful`, with the compatibility required by the original
statement. Exact faithful comparison reflects cohomology vanishing degree by degree on
arbitrary unbounded input. The last morphism is precisely the functorial image of the
canonical unbounded comparison unit, whose existing bounded-below invertibility theorem
applies to the underlying object of `L`.

Updated the item's DAG proof, proof dependencies, and proof origin to match this implementation;
removed obsolete tool-use entries. The existing closed node
`lem-weil-pbc-exact-functor-bounded-below` records the exact-functor cohomology API used for
comparison. It is a generic preliminary tool and does not replace any unit statement or step.
There are no new declarations or nodes and no definition/statement change record is needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.boundary_etale_adjunction_restriction`
(`lem-weil-boundary-etale-adjunction-restriction`).

Original item holes: 1. Remaining item holes: 0. Added holes: 0. Split-off statements: 0.
This is a proof from existing declarations, not a decomposition. Existing dependencies retain
their own proof status; no claims of closing their holes are made.

Single-file compilation passed in 9.8 seconds. Removed the two redundant tactics identified
by its linters; the delivery performs the final compilation and preflight checks.

## No longer needed

The following private proof imports are removed:

- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: the existing public
  compact-support module already supplies this extension-by-zero construction and exactness.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: use the existing derived
  exact-functor API instead of reproving the complex cohomology calculation.
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`: the fixed-module direct
  image already has the left-exactness instances required by the upper-amplitude theorem.
  Its separate constant-ring sheaf construction is unused.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`: the
  compact-support plus compatibility proves preservation of D+ without a new negative-degree
  vanishing calculation.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`: the standard fixed-module
  sheaf instances already supply the generic upper-amplitude theorem's hypotheses.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`: no separate constant-ring realization
  or enough-injectives construction is required; the existing fixed-module instance suffices.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`: the existing derived-category
  infrastructure supplies the K-injective-resolution instance used by the amplitude theorem.
- `Sheaf.SixFunctors.Etale.Derived.UpperShriekBoundedBelow`: its chosen-compactification
  interface is unnecessary; the same elementary orthogonality argument is written for the
  actual fixed compactification and its actual adjunction.
- `Sheaf.Paper.ComparisonPullbackExact`: the adopted comparison functor already has exactness
  instances and generic cohomology compatibility. The additional constant-ring scalar-extension
  normalization is unused. The mathematical exactness dependency remains in the DAG.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`: use the already-public
  `ProEtale.isIso_derivedComparisonAdjunction_unit_app` for the actual unbounded unit, directly
  on a bounded-below object. The mathematical site-comparison dependency remains in the DAG.

Removed these direct DAG proof dependencies (and their obsolete tool-use approvals):
`lem-weil-pbc-module-direct-image-left-exact`,
`lem-weil-pbc-derived-functor-negative-vanishing`,
`lem-pur-ringed-site-grothendieck-abelian`,
`lem-weil-pbc-module-sheaves-enough-injectives`,
`prop-weil-pbc-kinjective-resolutions-exist`, and
`lem-etale-upper-shriek-explicit-amplitude-interface`, for the reasons above.
No module is withdrawn and no adopted-source declaration or public import is removed.
Other consumers may still require all these modules; global pruning belongs to the maintainer.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was required. The plan was longer than the available API
requires: `rightDerivedLowerShriekOfCompactificationPlusCompatibility` already handles the
left functor's boundedness, while existing exact faithful comparison APIs handle arbitrary
lower bounds. The recorded exceptional-adjoint signature has obsolete Noetherian hypotheses;
the current adopted theorem is stronger and supplies the adjunction without them. We still
prove all the required Noetherianity conclusions.

The geometry includes the empty scheme and dimension bound zero. The upper-amplitude theorem
is applied to arbitrary upper-bounded input, without assuming it is also bounded below. The
right-adjoint lower bound is established before restriction. The comparison target's lower
boundedness comes from its canonical unit isomorphism, and the final mapped morphism uses
that exact unit, not an arbitrary isomorphism.

Read the item's source paragraph and the supplied dependencies, together with Stacks
`morphisms.tex`, lemma-finite-type-noetherian (01T6), `properties.tex`,
lemma-locally-Noetherian-quasi-separated (01OY), and `derived.tex`,
lemma-unbounded-right-derived (07K7), especially (4)(c). The Lean proof follows the existing
reviewed DAG route with the API simplifications described above. The unit record has no
realized statement or steps to bypass; its route is unchanged.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
