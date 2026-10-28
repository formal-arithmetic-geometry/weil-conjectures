## What changed

Added `Sheaf.Paper.ConstantAdicQuotientRealizationIsoLift` with the strictly
smaller point-stalk extraction theorem
`constantAdicQuotientRealization_iso_lift`, and imported it from the assigned
module.  The assigned theorem now applies this extraction and
`DerivedCategory.isIso_iff` to obtain isomorphisms on every homology object.
The item node proof and `proof_deps` now record the new extraction node.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.constantAdicQuotientRealization_homology_lift`.
The new theorem
`AlgebraicGeometry.Scheme.constantAdicQuotientRealization_iso_lift` remains as
one split `sorry`, recorded by node
`lem-weil-pbc-constant-adic-quotient-realization-iso-lift`.  Thus one of one
sorries in the assigned module was closed and one strictly smaller theorem was
split off.

## No longer needed

The assigned proof no longer imports
`Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism`; its parent
reflection module cannot be used here because it imports the assigned module.
The original proof dependencies remain the statement dependencies of the new
extraction theorem, while the assigned theorem itself depends only on the new
node.

## Where the brief, the DAG or earlier work was wrong

The planned proof step conflated extracting an algebraic morphism from a
realized isomorphism with the final derived homology criterion.  No existing
fullness or lifting theorem supplies that extraction, and the available
`constantRealizationReflectsIsomorphism` declaration only reflects a supplied
morphism and cannot construct one.  The extraction is therefore recorded as a
separate, strictly smaller statement; the parent proof is a genuine application
of the derived isomorphism criterion.

## New nodes

`lem-weil-pbc-constant-adic-quotient-realization-iso-lift` states the point-stalk
extraction step and is implemented by
`lean/Sheaf/Paper/ConstantAdicQuotientRealizationIsoLift.lean`.  No change
record is needed because the delivery adds only new declarations/modules and
proof imports in the assigned module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantAdicQuotientRealizationHomologyLift": "f0e7b622796b9af546009a7f17eb28cf400503c0", "Sheaf.Paper.ConstantAdicQuotientRealizationIsoLift": "d3f3c97dbab8ba234f2c84c2e00784476f8e8d81"}, "results": {"Sheaf.Paper.ConstantAdicQuotientRealizationReflectsIso": {"hash": "e5b0acd3604914f492bc6701aaabf0d54d771691", "status": "OK"}}, "seconds": 10, "time": "2026-10-28T08:03:17+0800", "transitive": 0, "version": 1}
```

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
