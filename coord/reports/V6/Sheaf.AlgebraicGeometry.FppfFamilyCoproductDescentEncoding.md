## What changed

Proved `AlgebraicGeometry.fppf_family_coproduct_descent_encoding` in its original module,
with its complete original statement. All four public definitions and both public imports
are unchanged. Added only proved private helpers and constructions.

The proof establishes universal coproduct cofans, constructs the singleton transport from
the represented component transitions, proves its naturality, identity and cocycle, recovers
the component points, and proves the realization equivalence for each fixed global scheme.
Existential quantification then gives equivalence of geometric effectivity.

The index universe is preserved: no `Small I` assumption was added. For any existing scheme
coproduct, the support of nonempty summands injects into its point space. Removing empty
summands therefore reduces the geometry to Mathlib's small-family coproduct results.
Empty summands are handled by initiality; the same argument covers an empty index type.

The singleton covering is proved fppf by the source locality of flatness and local finite
presentation on the coprojection open cover, then fpqc by Mathlib's existing inclusion.
Updated the existing node's proof and proof dependencies to this argument. No new public
interface or statement change, no adapted consumers, and no new nodes.

Validation: the complete module compiled cleanly through `lcompile.py` in 21.5 seconds
after import pruning, with no warnings or remaining holes. The delivery tool performs
the final preflight and axiom probe.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.fppf_family_coproduct_descent_encoding`
(node `lem-trf-fppf-family-coproduct-descent-encoding`).

Holes added: zero. Holes remaining in the item or packet: zero. Nothing was split off.
All private helpers have complete proofs; all private constructions use proved universal
properties or specified representability equivalences. No data are chosen from an
unproved existence theorem.

## No longer needed

Removed proof imports `Mathlib.AlgebraicGeometry.Gluing` and
`Sheaf.AlgebraicGeometry.FppfAffineRefinement`. Kept the proof import
`Mathlib.AlgebraicGeometry.PullbackCarrier` for the range of pullback projections.

The proof no longer uses node `lem-pc-fppf-affine-refinement` or its module
`Sheaf.AlgebraicGeometry.FppfAffineRefinement`: source locality makes the coproduct map
itself fppf, and Mathlib already proves fppf covers are fpqc. Removed its obsolete
`tool_uses` approval from the delivered node. Node `lem-trf-fppf-covering-base-change`
is also unnecessary in this proof because there is no separate affine-base refinement.

Node `lem-weil-pbc-scheme-morphism-gluing` is not used as a separate dependency:
Mathlib's disjoint-open-cofan colimit theorem and universal cofan API perform the assembly.
The underlying coproduct geometry and open-fibre-product nodes remain needed, as do all
the descent, scheme, fibre-product, flatness, fppf and fpqc definitions. No module is
withdrawn and no upstream declaration is removed. These are local dependency removals;
other parents may still require the pruned nodes.

## Where the brief, the DAG or earlier work was wrong

The old plan's affine refinement argument for fpqc membership is correct but unnecessary:
local finite presentation is local at source, so the coproduct singleton is fppf even
for infinitely many components. The original statement's weaker HasCoproduct hypotheses
also require care: Mathlib's direct sigma geometry assumes Small of the index type.
The support argument proves the needed geometry without strengthening the statement.

The original declaration docstrings are preserved verbatim; their proof sketch describes
the previous longer plan. The updated node records the actual proof. The unit route is
unchanged: this is the same family-to-singleton descent encoding support step.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
