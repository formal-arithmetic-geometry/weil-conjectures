## What changed

Proved `AlgebraicGeometry.ProEtale.reductionExceptionalRealization_exists` in
`Sheaf.SecSmoothPurity.ReductionExceptionalRealization` without changing its signature,
public imports, or the realization record. All added helpers are private and proved.
The proof constructs the actual site comparison equivalence on Dctf, restricts the
ordinary etale adjunction at the specified compactification, transports it through the
comparison equivalences, and verifies the exact prescribed counit equation.

Proof imports expose the existing private realization compatibility lemmas of
`ReductionDirectImage`, the native fixed-module Hom/Tor comparison APIs, ordinary
finite-ring exceptional preservation, compactification independence, and Mathlib's
fully faithful adjunction restriction. The source library is unchanged. The transport and prescribed counit calculation are
proved first for arbitrary categories and full subcategories. This keeps kernel
checking independent of the large concrete sheaf-functor definitions. A private
record bundles the ordinary right adjoint and its preservation proofs; its actual
constructor is irreducible, with all downstream access through the record fields.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.reductionExceptionalRealization_exists`
(node `lem-sp-reduction-exceptional-realization`). Added zero holes; no sorry remains
in the delivered module. This is a proof, not a decomposition. Existing imported
proof dependencies retain their own status.

The complete module compiled on the server in 12.5 seconds. Profiling and debugging
commands were then removed. The public theorem signature matches the original
verbatim; all lines meet the 100-character limit. The normal delivery performs the
final compile and preflight against current server sources.

## No longer needed

`det-pe-finite-tor-comparison-noetherian` and its module
`Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian` are not used by this
proof: the native fixed-module comparison and the already proved intrinsic
realization compatibility give the comparison equivalence directly. This is a
local dependency pruning; the module remains in the library and may have other users.

`def-weil-exceptional-inverse-image` and its general coefficient-system package are
not needed to construct this finite-ring adjunction. The proof uses the ordinary
etale adjunction directly. `def-sp-finite-intrinsic-direct-adjunction` records the
actual realization equivalences used instead.

The general localizing exceptional-adjoint preservation theorem is not applied.
As the previous plan specified, only the ordinary etale preservation results
underlying `sk-prop-sf-rf-shriek-preservation` are used. No chart, scalar-extension,
Tate-line, or coefficient-system construction is added to the argument.

The original public import of ReductionExceptionalObjects is retained because it
supplies the statement's definitions. No existing library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old DAG reported that the counit transport still needed formalization after a
kernel-limit failure. A general full-subcategory transport theorem separates that calculation from
large sheaf definitions: naturality, full faithfulness, and the equivalence triangle
identity suffice. Merely factoring the counit formula was insufficient: its concrete
application still triggered expensive kernel conversion. Abstracting the whole
transport construction and explicitly substituting the prescribed comparison remove
that conversion from the concrete proof. The comparison is first bound as a variable
with an equality to the original; rewriting by this equality proves the exact
original counit equation without normalizing the closed comparison construction.
The resulting output comparison is the identity between definitionally equal functors.

The historical build-error record says the Objects import failed. The current live
queue classifies this item as a proof task; its current statement has one hole.
The proof compiles against the published dependency artifacts; the normal delivery
check validates it against current server sources.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 5 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SecSmoothPurity.ReductionExceptionalRealization": "2cd75bb7fc7e0bbc4976e5b3f2de4501ddc3f4c7"}, "results": {"Sheaf.Paper.CompositeProjectionCoefficients": {"hash": "58bccbe5e63d9c75f3a8a435f54da0ddfad9a560", "status": "OK"}, "Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons": {"hash": "a09ffd92bfcb32abe2cfcdf4d36409c922bbff13", "status": "OK"}, "Sheaf.Paper.FieldPurityTransposeArrows": {"hash": "bd6e29a7c71ad614a10743bd1517519239715b5d", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerGluingData": {"hash": "0bea1424c4eade65d219cb1a6fe2d5803e4702c8", "status": "OK"}, "Sheaf.SecSmoothPurity.ReductionExceptional": {"hash": "b80f17c7b85d282f0e2f46a9482d4abe6835b64c", "status": "OK"}}, "seconds": 97, "time": "2026-10-28T01:22:07+0800", "transitive": 4, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
