## What changed

Completed `AlgebraicGeometry.Scheme.finiteRing_constructibleDerived_origin` in
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`, retaining its entire public signature
and all public imports. The retained sandbox proof compiles against the current library.

The proof factors the specified intrinsic comparison as fixed-module comparison followed
by intrinsic realization. Three proved private helpers identify realization followed by
constant-scalar restriction, compare the constructibility predicates, and transport
intrinsic constructibility across isomorphisms. The first helper constructs its isomorphism
from the canonical sheafification counit; it does not choose an arbitrary coefficient
identification.

Fullness and faithfulness follow by restricting the existing derived Hom bijection to the
bounded constructible source. Exact homology comparison proves the forward image criterion.
For the converse, transfer through the realization equivalence, descend the constructible
cohomology sheaves, and apply the existing
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible_of_homology`. Convert its
source constructibility predicate with the existing finite-ring comparison and its two
bounds with `min` and `max`. Exactness and faithfulness preserve and reflect vanishing in
each degree, proving the last interval assertion without an assumption that the endpoints
are ordered.

The source and project constructibility predicates both retain global finite
stratifications. The restriction comparison handles the positive-stratum convention even
on an empty scheme. No nonzero-ring or nonempty-scheme assumption is introduced.

Added proof imports:
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`;
- `Sheaf.Paper.ProEtaleConstantModuleConstructibility`;
- `WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`;
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect`.

Updated the item's proof route and registered two already-existing source theorems as nodes.
No existing statement or definition changes, consumer adaptations, or change records are
needed. The public theorem signature was also compared textually with the current source.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finiteRing_constructibleDerived_origin`
(node `lem-weil-pbc-finite-ring-constructible-derived-origin`).

Original holes: 1. Holes closed: 1. Holes added: 0. Holes remaining in delivered Lean: 0.
Split-offs: 0. This is a proof from existing declarations, not a decomposition into new holes.
The three private helpers are all proved.

Existing dependencies remain conditional on their own pre-existing obligations, including
`AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_exact` and comparison
injective acyclicity. The two new node records register complete existing theorem bodies;
they do not assert that the transitive axiom dependencies are already closed.

Validation: the retained proof passed `deliver3.py --no-push`, including compilation and
preflight. The final version additionally retains the unit-route comparison import and
uses its theorem explicitly for exactness; its validation is recorded by the final dry run.
The unchanged signature includes every finite commutative ring and arbitrary scheme. Empty intervals are handled degreewise, and the conversion from
separate bounds to an ordered interval uses minimum and maximum.

## No longer needed

Removed direct proof imports:
- `Sheaf.Paper.FiniteRingConstructibleSheafOrigin`;
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`;
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`;
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`;
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`;
- `Mathlib.CategoryTheory.Triangulated.Triangulated`;
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`;
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`.

The Mathlib APIs are still available through the existing imports. The current source
also imports compact-support comparison and finite-module encoding directly; their APIs
needed by this proof are already available through the retained imports, so these direct
proof imports are removed as well. The proof does not use
`lem-weil-pbc-finite-ring-constructible-sheaf-origin` or its module: the established
fixed-module origin theorem plus restriction constructibility give exactly the required
cohomology witnesses without packaging an additional sheaf equivalence. It retains and
directly applies
`prop-weil-pbc-site-comparison-finite-level` for exactness of fixed-module comparison,
because that node realizes a step of `sk-prop-pe-comparison-morphism`. This preserves
the blueprint unit route while the remaining interval argument uses degreewise exactness
and faithfulness.

Removed the following direct proof-dependency edges from the item:
`def-weil-triangulated-category`, `lem-sf-derived-concentrated-single`,
`lem-sf-derived-homology-long-exact`, `lem-sf-derived-truncation-triangle`,
`lem-sf-exact-functor-derived-triangulated`, `lem-sf-triangle-morphism-iso`,
`lem-weil-pbc-finite-ring-constructible-sheaf-origin`, and
`thm-weil-pbc-site-comparison`.
The derived devissage facts are implemented by the existing bounded-constructible-origin
and derived-Hom theorems; their relevant dependencies are retained under the new nodes.
This removes duplicate work in this module rather than claiming that every such module is
unreachable from all project targets. No unit statement or realized proof step is bypassed;
the item's node is below the unit's own realized nodes.

## Where the brief, the DAG or earlier work was wrong

Delivery infrastructure failure on 2026-10-19: the required `deliver3.py --no-push`
was attempted twice. Both attempts exited with `subprocess.TimeoutExpired` in
`sharedrepo.worktree`, running `git checkout -q --detach origin/sheaf-dag` with
a 600-second timeout. This occurred before preflight or compilation of the delivery.
The second attempt ended at approximately 01:19 CST. No push was attempted then.
On resuming at 02:10 CST, the required dry run passed at 02:15 CST; the earlier
worktree failure is resolved. No launcher
script or shared repository file was modified.

The retained sandbox already contained a complete proof, but no report or delivery.
Its two new node records incorrectly labeled the reused source theorems as transitively
closed. Removed those unsupported audit records: the complete proof bodies may still rest
on existing holes, as the project's stage-3 contract permits.

The original seven-step route need not be reimplemented: the source library already proves
the bounded constructible devissage and the required derived Hom bijection. The necessary
additional work is the explicit comparison with intrinsic realization, since an abstract
unrelated equivalence would not identify the specified inverse-image functor. The existing
source theorem `isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf` has exactly the
finite-ring comparison needed here; no new predicate or weaker theorem is introduced.

## New nodes

`lem-weil-pbc-fixed-module-derived-hom-bijection` records the existing theorem
`AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`.
Only the target of a Hom needs to be bounded below. Its source proof uses the comparison
unit and derived adjunction; its existing injective-acyclicity dependency remains recorded.
No Lean declaration or hole is added.

`lem-weil-pbc-fixed-module-bounded-constructible-origin` records the existing theorem
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible_of_homology` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect`.
Its source proof uses triangulated closure of the bounded constructible image and bounded
devissage. It supplies exactly the fixed-module bounded origin used in the converse image
criterion. No Lean declaration or hole is added.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
