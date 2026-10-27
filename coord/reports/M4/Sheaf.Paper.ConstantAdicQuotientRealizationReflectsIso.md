## What changed

The target module now imports the new homology-level lift module and proves
`AlgebraicGeometry.Scheme.constantAdicQuotientRealization_reflects_iso` by applying
the lift and `DerivedCategory.isIso_iff`.  The new module
`Sheaf.Paper.ConstantAdicQuotientRealizationHomologyLift` records the remaining
stalk and coefficient-transport step as one named public theorem with `sorry`.
The target's copied DAG node now records this proof route.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.constantAdicQuotientRealization_reflects_iso`.

One hole was added as a strict decomposition:
`AlgebraicGeometry.Scheme.constantAdicQuotientRealization_homology_lift`, in
node `lem-weil-pbc-constant-adic-quotient-realization-homology-lift`.
The new theorem produces an algebraic morphism and proves that every induced
cohomology map is invertible; the target then combines these maps using the
unbounded derived isomorphism criterion.

## No longer needed

Removed the unused proof-only import
`Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism` from the target
module after the proof was reduced to the new homology-level theorem.  The
scalar-comparison import remains public because the target statement uses its
definitions.  No existing dependency node is otherwise pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG grouped the geometric stalk transport and the derived
isomorphism criterion in one unproved statement.  The delivery separates the
stalk transport into a strictly smaller homology-level lift and makes the
criterion application explicit.  No target signature was changed.

## New nodes

`lem-weil-pbc-constant-adic-quotient-realization-homology-lift` records the
remaining nonempty-chart stalk and coefficient-transport argument.  Its Lean
declaration is in
`lean/Sheaf/Paper/ConstantAdicQuotientRealizationHomologyLift.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantAdicQuotientRealizationHomologyLift": "71a3fc33abf94cab77e99e1312d95c960d9976b1", "Sheaf.Paper.ConstantAdicQuotientRealizationReflectsIso": "e5b0acd3604914f492bc6701aaabf0d54d771691"}, "results": {"Sheaf.Paper.ConstantAdicQuotientModelExtensionIso": {"hash": "9698fc5ea81194d9f0ee084bcbbc3e44f9550a95", "status": "OK"}}, "seconds": 12, "time": "2026-10-28T06:27:26+0800", "transitive": 0, "version": 1}
```

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
