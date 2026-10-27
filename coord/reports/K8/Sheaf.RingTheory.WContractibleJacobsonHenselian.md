## What changed

Proved `RingTheory.wcontractible_jacobson_henselian` in
`Sheaf.RingTheory.WContractibleJacobsonHenselian`, with its statement unchanged.
Added a proved private helper `RingTheory.henselian_of_retraction` to descend
simple polynomial roots along a ring retraction. The main proof constructs the
pair henselization, proves it ind-etale and faithfully flat, and applies the
existing w-contractible retraction theorem. It descends henselianity directly
and uses the already proved integral-algebra idempotent-lifting theorem for the
finite-algebra clause. No definitions or public interfaces changed.

Updated the node proof, proof dependencies and proof origin to match the Lean.
Removed the obsolete top-level `det-pe-wlocal-components` tool approval.
The integral-algebra lifting dependency is already Lean-closed and is used as a
tool for the explicit idempotent clause; no new unproved result is introduced.
The unit's compactification comparison/coherence route is unchanged.

Validation: the complete module compiled through `lcompile.py`, without warnings.
The proof imposes no nontriviality assumption; the zero ring has no maximal
ideals to check. The finite algebra may also be zero, and its universe remains
`max u v` as in the original statement.

## Proved and sorry left

Closed 1 of 1 original holes:
`RingTheory.wcontractible_jacobson_henselian`
(node `lem-sfb-wcontractible-jacobson-henselian`).

Added 0 holes and split off 0 statements. There are no `sorry`s left in the
assigned module or anywhere in this delivery. The private retraction helper is
fully proved. The proof uses the existing pair-henselization declarations as
supplied by the library; no claim is made to close their dependencies.

## No longer needed

Removed imports:
- `Sheaf.RingTheory.IndEtaleUniverseTransport`: the henselization and R are
  already in the same universe; use the existing ind-etale predicate directly.
- `Sheaf.Topology.WLocalComponents`: the source `IsWContractibleRing` class
  already has `IsWLocalRing` as a superclass.
- `WeilConjectures.RingTheory.ProEtale.WLocal`: no direct use beyond the
  superclass already publicly imported by WContractible.
- `WeilConjectures.RingTheory.PairHenselization`: redundant direct import;
  PairHenselizationFlatQuotients publicly imports it, and the theorem remains used.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: redundant direct import;
  already exposed by the statement's WContractible dependency.

Removed proof dependencies `det-pe-wlocal-components` and
`def-weil-pbc-w-local`; no additional topology comparison is needed in this proof.
The former is also removed from the node's top-level tool approvals.
The old tensor-product descent construction in steps 5–7 is unnecessary:
simple-root descent plus the proved integral-algebra idempotent theorem suffices.
No module is withdrawn, and no claim of global unreachability is made.

## Where the brief, the DAG or earlier work was wrong

The old plan required a separate comparison of the two descriptions of
w-locality. In the actual Lean interface `IsWContractibleRing` extends
`IsWStrictlyLocalRing`, which extends `IsWLocalRing`, so the retraction theorem
applies directly. Also, the recorded HenselianRing predicate has a simple-root
field, so descent can be proved with polynomial maps rather than constructing
and comparing tensor-product idempotents.

No statement repair or forced consumer adaptation was necessary. No new nodes.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
