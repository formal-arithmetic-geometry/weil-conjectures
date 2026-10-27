## What changed

Added the proved theorem
`AlgebraicGeometry.ProEtale.uniformConstructibleExt_latticeModel` to the assigned module.
It chooses the finite coefficient model of the lisse source once, with the actual pinned
coefficient morphism and scalar-extension isomorphism. If that very model admits a global
lisse integral lattice, it proves the exact original natural-number cutoff
`cd_ell(j) + cd_ell(S) + 2` against every constructible target. The proof uses the final
conditional clause of `uniformConstructibleExtRational`, the proved cutoff-finiteness
theorem, and covariant Ext exactness along the actual coefficient-heart target filtration.
It factors each target stratum through its image and transports its quotient isomorphism.
The cutoff and finite coefficient model are independent of the target.

The rational module becomes a public import because its actual lattice type and integral
inclusion occur in the new public signature. Every original signature and proof is
unchanged, including the original disputed theorem. No definition, instance, attribute,
source-library module or target is changed. The item node records this additional proved
step and the remaining obstruction. There are no new nodes or split-off statements.

Change record: `coord/changes/D9-uniform-ext-lattice-model.md`, including the transitive
consumer inventory. Only the assigned existing module and its node are edited. The two
current direct importers are compiled from unchanged temporary sandbox copies, which are
removed before delivery.

Validation: the single-file compile passed (24.3 s). A compile set containing the item
and both unchanged direct importers passed with exit code 0 for all three modules.
The compile service accepted every file under its per-file limit; the longer elapsed
figures printed for the set include setup and cache-lock work outside the timed Lean run.
The final theorem body and every existing public signature were compared byte-for-byte
with the source and are unchanged. The node's proof-dependency union still matches its
recorded dependency list. All Lean lines have at most 100 characters.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added: **0**. Split off: **0**. Net hole change: **0**.
This is a partial proof of the supported explicit-cutoff case, not a complete proof or a
decomposition of the unconditional theorem.

Newly proved from the existing declared dependencies:
`AlgebraicGeometry.ProEtale.uniformConstructibleExt_latticeModel`, attached to
`sk-lem-uniform-constructible-ext`. Its proof contains no hole and does not invoke the
original disputed theorem. Existing completed proofs of `uniformConstructibleExt_exists`
and `uniformConstructibleExt_cutoff` are retained verbatim.

The sole remaining direct hole is
`AlgebraicGeometry.ProEtale.uniformConstructibleExt`, node
`sk-lem-uniform-constructible-ext`. Its original whole-proof `sorry` is retained. No hole
is moved into another theorem, a private declaration or a data definition.

## No longer needed

None. No module, node or import is withdrawn. In particular, the rational stratum estimate,
its refined-cutoff construction and all of its dependencies remain needed. No unit step
is bypassed. The rational import is promoted to public rather than removed, because its
lattice construction is now part of the proved public conditional statement.

## Where the brief, the DAG or earlier work was wrong

The existing STATEMENT-DISPUTED annotation remains unresolved: the unconditional explicit
cutoff does not follow from the repaired rational theorem's refined maximum. That theorem
only supplies the unrefined estimate conditional on a global lisse integral lattice in its
fixed finite source model. The original item does not assume such a lattice, and the
stratified-lattice theorem provides lattices only after a finite stratification. A
constructible integral model need not be a lisse integral lattice on the whole source.
The new proof supplies the target-filtration step under exactly the existing conditional
hypothesis; it neither supplies that hypothesis nor asserts the unsupported comparison
between refined and unrefined cutoffs. This is a proof/interface gap, not a certified
counterexample to the unconditional Ext assertion.

The current source exists, despite its historical quarantine row in `coord/rework.tsv`.
It was copied from the current source and compiled before editing. No quarantine archive,
Lean attachment, parent dependency or public declaration is deleted.

Edge checks: the zero target and empty target filtration are handled by zero-object Ext
vanishing; rank-zero lattices and empty strata cause no new premise; the two base fields
are treated by their actual field isomorphisms and characteristic transport. The displayed
cutoff is finite by the existing finite-type dimension argument. The target filtration
length never enters the cutoff. Both coefficient choices use the same fixed-model
conditional returned by the rational theorem.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
