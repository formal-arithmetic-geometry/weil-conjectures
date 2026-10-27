## What changed

Restored `Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion` from its designated
quarantine archive. Replaced its stale public import of the withdrawn
`Sheaf.AlgebraicGeometry.PerfectDescentOnOpen` with the authoritative
`WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen`. This fixes the recorded
`HasDerivedCategory` visibility failure. Removed two redundant private imports
listed below. The theorem signature, docstring, categorical helper, main proof,
DAG node, Lean attachment and five proof dependencies are unchanged.

Change record: `coord/changes/perfect-descent-open-union-public-import.md`.

The restored module compiles cleanly through `lcompile.py` in 27.2 seconds,
with no warnings. Byte comparison confirms that only the three import lines
differ from the quarantine archive; all proof bodies and signatures are verbatim.

## Proved and sorry left

This is a zero-hole rework restoration, not a new hole closure. The archive and
the delivered module both contain zero `sorry`s. Holes closed: none (0 of 0).
Holes added: none. Split off: none.

`AlgebraicGeometry.perfect_descent_open_union` (node
`lem-pc-perfect-descent-open-union`) retains its complete proof from compatible
local data, derived open gluing, local perfect-model transport, adjunction
naturality and local detection of derived isomorphisms. The private helper
`AlgebraicGeometry.isIso_restricted_adjoint` also retains its complete proof.
No additional proof of downstream dependencies is claimed.

## No longer needed

Replaced the empty public import
`Sheaf.AlgebraicGeometry.PerfectDescentOnOpen` by its source-library counterpart.
Removed redundant private imports
`WeilConjectures.AlgebraicGeometry.DerivedCategory` and
`WeilConjectures.AlgebraicGeometry.PerfectComplex`; both already occur in the
public dependency closure of the corrected import. Their mathematical notions
remain needed. No DAG node, theorem, or proof-dependency module is pruned.

## Where the brief, the DAG or earlier work was wrong

The rework diagnostic is accurate: after upstream duplicate retirement the
archived public import exposes no declarations. Merely retaining its private
proof imports cannot elaborate the public theorem's statement. The corrected
public import restores the intended interface without changing any hypothesis
or conclusion. The absent live source is quarantined, not withdrawn; its parent
`Sheaf.AlgebraicGeometry.PerfectComplexDescent` remains a genuine consumer.

The original archived parent was also checked against the restored module.
Its public statement independently fails on `derivedPullback`, since its own
public import names the withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback`.
That pre-existing parent rework is outside this import-visibility repair.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
