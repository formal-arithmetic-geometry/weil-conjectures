## What changed

Implemented the six-conjunct proof of
`WeilConjectures.sfIntegralDirectImage_constructible` in
`lean/Sheaf/Paper/SfIntegralDirectImageConstructible.lean`. Its mathematical signature,
public imports and all definitions are unchanged. The unused-instance-name linter
is disabled only for the original public theorem so its binder names stay verbatim.

The proof constructs a Roos direct image from countable products; transports finite
constructibility between fixed and intrinsic coefficient presentations; proves the
nilpotent-kernel calculation for the lifted quotient map; transfers the residue bound
to every positive level; handles arbitrary integer bounds, empty input intervals,
and the empty source; and assembles integral constructibility by the defining
predicate. The arithmetic, coefficient equivalence and interval glue is written out
as proved private helpers. The source library is untouched.

Added `lean/Sheaf/Paper/SfCompleteDirectImageReduction.lean` for the separate,
geometry-independent source result on complete direct images and canonical finite
reductions. This is the remaining part of the argument, stated with its source and
complete natural-language proof. It applies to any scheme morphism and any complete
complex, without finite type, a base field, constructibility, or amplitude bounds.
It combines Stacks 099N(1),(3),(4) with the perfect-coefficient projection formula
0944, in the exact coefficient and projection models used by the item.

Updated the item node's proof route and dependencies, and added the matching node
for this source result. No definition/statement repair or forced adaptation is made.

Validation: `lcompile.py` compiled the new interface module (2.7 s) and the full
item module (40.7 s, clean exit 0, no warnings). The delivery repeats the required
compilation, axiom and preflight checks.

## Proved and sorry left

Closed the original body hole of
`WeilConjectures.sfIntegralDirectImage_constructible` (one original hole).
Its assembly, finite constructibility, explicit nilpotent devissage, uniform bounds,
and edge cases contain no `sorry`.

Added one hole: `WeilConjectures.sfCompleteDirectImage_reduction`, node
`lem-sf-complete-direct-image-reduction`. Its body is exactly `by sorry`.
The unresolved work is the normalized transfer from the published generic
completed-coefficient/limit interfaces to `sfCompletedDerivedDirectImage`, and then
to every chosen `SfIntegralDirectImage` triangle and its specified projection adjuncts.
The new statement is a strict part of the argument, not the original constructibility
theorem under another name: it has no finiteness assertions or cohomological bounds,
and the several geometric and amplitude conclusions require the independent Lean
arguments in the item module.

Counts: 1 original body closed; 1 new body left. This is a decomposition, with zero
net holes closed, not a proof of the entire target closure. Existing admitted finite
constructibility and coefficient-comparison dependencies are used as declarations;
none is newly admitted or weakened by this delivery. No holes occur in definitions.

## No longer needed

The following original private proof imports are removed from the item module:

- `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.EtaleHigherDirectImageStalkCriterion`
- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `WeilConjectures.RingTheory.Etale.LocalDimension`
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.Paper.RestrictionOfScalarsExact`
- `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`

The main proof no longer directly needs these old planned dependencies:

- `def-kun-cd`
- `def-weil-derived-direct-image`
- `def-weil-pbc-adic-coefficient-datum`
- `lem-kun-0f10`
- `lem-kun-dimension-extension`
- `lem-kun-torsion-abelian-direct-image-dimension-bound`
- `lem-pur-completed-coefficient-pushforward-comparison`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `prop-weil-pbc-direct-image-limits`

The completed-coefficient comparison, adic datum, and direct-image/limit theorem are
still needed below the new completion node; they are moved out of the geometric
assembly, not withdrawn. The torsion-abelian bound and its abelian-forgetting detour
are replaced by the already proved torsion-module estimates in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension`.
The coefficient-change vanishing lemma remains needed for the quotient-ring
isomorphism in the nilpotent argument.

The high-level `Sheaf.Paper.IntegralOperationsWellDefined` import was also avoided:
the few product-instance steps are derived directly from the existing exact-product
and derived-product theorems. No theorem of that package is withdrawn.

Deleted these obsolete top-level tool-use entries from the item node (remaining
approvals keep their original order):

- `lem-kun-0f10`
- `lem-kun-cd-stalk-criterion`
- `lem-pc-right-derived-functor-triangulated`
- `lem-sc-etale-local-dimension`
- `lem-sf-derived-homology-long-exact`
- `lem-sf-derived-truncation-triangle`
- `lem-sf-proetale-constructible-origin`
- `lem-sf-separably-closed-torsion-cd`
- `lem-weil-pbc-profinite-coefficient-inverse-image`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `lem-weil-restriction-of-scalars-exact`
- `prop-weil-pbc-comparison-direct-image`
- `prop-weil-pbc-direct-image-limits`
- `thm-dg-finite-type-constructibility`
- `thm-sc-finite-type-torsion-cd`
- `lem-kun-dimension-extension`
- `lem-kun-torsion-abelian-direct-image-dimension-bound`
- `lem-pur-completed-coefficient-pushforward-comparison`

These are route/import removals for this item. Their modules may remain imported
transitively or used by other parents; no global module withdrawal or source-library
declaration deletion is claimed. The admissibility unit has only its realized
statement, and its route is preserved.

## Where the brief, the DAG or earlier work was wrong

The current DAG has the newer nine-step assembly, while the original Lean docstring
still described its older unsplit argument. The docstring and delivered node now
follow the implemented proof.

The generic completed-coefficient comparison and direct-image/limit declarations
use different coefficient presentations and universal derived models from the sf
interface. Their preservation claims cannot be applied to the sf object by `exact`:
one must identify structural maps through finite projections, transport normalized
right-derived comparisons and adjunction units, and compare Roos triangles with their
projections retained. The new source node records precisely this remaining part.

The explicit source-library torsion-module estimates give both uniform and algebraically
closed bounds directly; no new torsion-abelian finiteness lemma is necessary. The
empty-source argument uses Krull dimension at most zero, including the bottom value;
it does not assume the empty scheme has natural dimension zero. The support proof
retains arbitrary integer N and the case a>b.

## New nodes

`lem-sf-complete-direct-image-reduction` (module
`Sheaf.Paper.SfCompleteDirectImageReduction`) records Stacks 099N and 0944 for an
arbitrary morphism in the specified sf coefficient model. The source statement is
strictly separate from constructibility and uniform cohomological amplitude. Its
source dependencies are already stated; its docstring explains normalization,
completeness preservation, perfect reduction, and triangle comparison, including
empty schemes and zero complexes. The blueprint ancestor is
`def-weil-ordinary-compact-cohomology`, through the integral constructible codomain
of its ordinary direct image. Searches for `099N` find the generic adic theorem;
searches for the sf normalized result find no existing node. Four actual Mathlib
searches are recorded, including each required family (LeanSearch, LeanFinder/Loogle,
and Mathlib source grep). No change record is needed because existing definitions and
mathematical statements are retained.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
