## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.henselian_lisse_rigidity` in
`Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity`, preserving its statement and all
existing definitions and public imports. The proof obtains the component homeomorphism
from unique idempotent lifting and the clopen criterion, transports w-strict locality and
extremal disconnectedness, and constructs the equivalence of dualizable subcategories
from the component square.

Proved private helpers supply the categorical glue: module transport along a monoidal
equivalence, restriction of monoidal equivalences to dualizable objects, continuous slice
pullback along an isomorphism, and reconciliation of the independently supplied component
coefficient isomorphisms by an exact monoidal scalar automorphism. The latter ensures that
the square uses the actual component functors, rather than assuming their chosen
coefficient comparisons coincide. The resulting scheme equivalence is the lift of the
prescribed derived inverse image, so its inclusion comparison is reflexive.

Updated the item's DAG proof and proof dependencies to describe this assembly. There are
no changes to source-library files, public interfaces, or consumer modules.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.henselian_lisse_rigidity`
(`lem-zl-condensed-henselian-lisse-rigidity`).

Holes closed: 1. Holes added: 0. Sorries left in the delivered Lean module: 0.
No split-off statements or new modules. Existing stated component compatibility and
component square theorems remain dependencies, as intended by stage 3.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation` and
its direct dependency `lem-zl-condensed-wcontractible-lisse-evaluation`: only its component
compatibility clause is needed, and the existing
`Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility` theorem supplies that
clause for the precise continuity and tensor witnesses of the component square. The
broader evaluation assertions about scalar realization and perfect section complexes
are unnecessary for this proof.

Removed redundant proof imports `WeilConjectures.Mathlib.RingTheory.Henselian` and
`WeilConjectures.Topology.SpectralSpace.ConnectedComponent`. The henselian predicate is
already available through the hypotheses' imports; the full connected-component
separation proof is supplied by the existing clopen homeomorphism criterion. The
idempotent/clopen dictionary and spectral clopen criterion remain used.

The separate direct citation of `lem-zl-component-lift-base-change` is unnecessary here:
`lem-zl-component-derived-pullback-square` already packages its induced derived natural
isomorphism. The lift node and module remain needed by that square; they are not withdrawn.
Also removed the obsolete top-level tool approval
`lem-weil-pbc-quasicompact-components-clopen-intersection`: the proof uses the recorded
spectral clopen homeomorphism criterion, which already contains the separation argument.
No module is withdrawn, and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The first planned step described unique idempotent lifting as immediate from the recorded
henselian definition. The Lean predicate is the simple-root-lifting definition. The
existing proved `Algebra.existsUnique_isIdempotentElem_of_henselianRing` supplies the
required implication, and is now explicitly recorded as a proof dependency.

The evaluation and component-square interfaces independently choose coefficient
isomorphisms. Their equality is not an available hypothesis. Restriction of scalars along
the composite automorphism reconciles them without changing either interface. The DAG
now records this glue. Empty spectra and the zero coefficient ring are included: neither
the topology proof nor any categorical cancellation assumes nonemptiness.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
