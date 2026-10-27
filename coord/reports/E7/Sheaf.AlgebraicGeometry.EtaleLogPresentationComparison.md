## What changed

Proved `AlgebraicGeometry.etaleLogPresentation_comparison` in the assigned module,
with every existing public declaration signature and definition body preserved.
Six proved private helpers establish naturality of structural stalk maps, functoriality
of prelog stalk maps, naturality of inverse unit identifications, the elementary
surjective-pair-map/kernel argument, the comparison with set stalks, and conservativity
for monoid sheaves. The main proof explicitly constructs the compatible-Hom equivalence
and transfers both injectivity and the exact compatible range.

The pair formula at `(1,1)` proves `prelogSectionUnit K W 1 = 1`; its specialization
at `(m,1)` then proves `f i = v`. Structural compatibility forces the map on each stalk
to preserve its inverse unit identification. Consequently both canonical pair maps
commute with this stalk map, and their stated surjectivity and equal kernels prove
bijectivity directly. No arbitrary witness or presentation is chosen from an unproved
existence theorem.

Updated proof steps 5--7 and their dependency union in
`lem-trf-etale-log-presentation-comparison`; steps 1--4 remain the restriction theorem's
original proof plan. The unit record has no realized statement or step attached to
this node, and its route is preserved. All changes are confined to the item and its node.

Validation: remote single-file compilation passed in 7.8 seconds before import cleanup;
the final version is checked again by `lcompile.py` and `deliver3.py`. Sources read:
ILO VI 1.1, printed p.69 (PDF p.75), and Stacks `theorem-exactness-stalks` (03PU).
Mathlib signatures inspected include set-stalk conservativity, the colimit preservation
comparison and its naturality, filtered final models, and units-map composition.
The prescribed searches used leanfinder, loogle and grep through `msearch.py`, together
with local searches in both library roots and Mathlib. No existing theorem already
proved this log-presentation comparison.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.etaleLogPresentation_comparison`.

One original hole remains, unchanged:
`AlgebraicGeometry.etaleLogPresentation_restriction`
(node `lem-trf-etale-log-presentation-comparison`). Its original source, full proof
in words and exact statement remain in the module. This is the brief's permitted
partial delivery for a module containing several holes, not a decomposition.

Added zero holes and zero split-off theorems. Every new private helper is proved.
Imported statements and proof fields retain their existing dependencies; this does
not claim that the targets' transitive axiom closure is already free of `sorryAx`.

## No longer needed

Removed proof-only imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `Mathlib.CategoryTheory.Sites.CoverLifting`
- `Mathlib.CategoryTheory.Limits.Types.Filtered`

The actual comparison proof does not use the unit-representative or pushout-comparison
theorem `lem-trf-filtered-ring-log-pushout`
(`Sheaf.RingTheory.FilteredRingLogPushout`). It also does not use the elementwise
representative lemmas `lem-weil-pbc-filtered-colimit-sets-elementwise`, or the separate
common-neighbourhood argument of `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`.
Removed these three explicit dependencies from this node's proof-dependency union,
and removed the latter two obsolete entries from its top-level `tool_uses`, preserving
the order of the other approvals. Cofilteredness is still present implicitly in the
existing geometric-stalk definitions and filtered-final-model infrastructure; no
foundational indexing instance has been removed.

The restriction theorem still needs its original geometric and sheafification plan.
No declaration, file, unit step or module is withdrawn, and no source-library
interface is altered. The unused modules listed above may have other consumers.

## Where the brief, the DAG or earlier work was wrong

The original comparison plan is valid but unnecessarily passes to simultaneous
section representatives and ring-unit representatives. The existing log axiom on
stalk unit groups already forces preservation of the canonical units, and the
existing `IsStalkChart` predicate supplies the exact kernel needed. This yields a
shorter complete proof without importing any additional unfinished theorem.

The comparison's sheafification and structural-pair hypotheses for L are redundant
once the given stalk-chart hypotheses and pair formula are available. They are
retained verbatim. The original comparison docstring records the earlier valid
representative proof; the updated DAG records the shorter proof actually implemented.

The public geometric-stalk interface deliberately avoids requiring all colimits
in commutative monoids. The proof respects this: it constructs preservation only
for the required pointed-neighbourhood shape, using its small filtered final model,
and applies the conservative family only to the underlying set sheaves.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
