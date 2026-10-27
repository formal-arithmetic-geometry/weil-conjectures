## What changed

Marked `AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothTrace` as
`STATEMENT-DISPUTED` in its declaration.  No proof or import was added.

## Proved and sorry left

No original holes were closed.  The theorem's single `sorry` remains, because
its `∃!` conclusion is false as written; no new `sorry` was added.

## No longer needed

None.  The existing imports and DAG dependencies remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The uniqueness clause confuses existence of an adjunction transpose with
uniqueness of a representing morphism.  If `t` satisfies the displayed
bijectivity condition and `σ : M ≅ M` is an automorphism, then
`F.map σ.hom ≫ t` satisfies it as well: postcomposition by the functorial image
of `σ` merely precomposes the bijection by the bijection
`(a : K ⟶ M) ↦ a ≫ σ.hom`.  The hypotheses contain no normalization that forces
`σ = 𝟙`.  In the identity smooth map of relative dimension zero, the coefficient
unit has scalar automorphisms; over the characteristic-zero condensed coefficient
ring, `-𝟙` is a nontrivial example.  Thus the two resulting traces are distinct
while both satisfy the stated condition.  The geometric route can establish a
representing trace (or an isomorphism with the exceptional unit), but cannot
prove this unconditional uniqueness statement.  The target signature is kept
unchanged as required.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SmoothPurity.TraceExistence": "b7f0f34d60cdae6bd6ee12993751c7385a002e28"}, "results": {}, "time": "2026-10-28T07:14:17+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
