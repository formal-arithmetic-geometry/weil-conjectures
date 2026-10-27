## What changed

Repaired the running-global-build failure in
`Sheaf.Paper.ConstructibleRingLeftRefinement.exists_ring_left_refinement` (in namespace
`WeilConjectures.ConstructibleExceptionalCoefficients`). The integral scalar square previously
called `cancel_mono` on the composite of a component of `R.left` and the proper image of a
component of `SX.realization`. Typeclass synthesis for that composite exhausted its 20000
heartbeat budget against the current dependencies.

The proof now supplies that composite as the explicit isomorphism
`(R.left d (.integral L)).app (SX.functor.obj K) ≪≫ Hd.mapIso (SX.realization.app K)`
and applies Mathlib's `Iso.cancel_iso_hom_right`. Its forward map is exactly the previous
cancellation morphism; three projection lemmas put it in the explicit composite form before
the subsequent normalization and scalar-word calculation.
Only these proof lines changed: there is no interface, definition, instance, attribute, option,
or import change. The existing DAG proof and dependency list still describe this proof.

## Proved and sorry left

This is a zero-hole build repair. Holes closed: 0. Holes added: 0. Holes remaining in the
item: 0. The existing complete proof of
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_left_refinement`
is retained, with the failing cancellation repaired. Nothing is split off.

The existing dependencies `exists_ring_open_refinement` and
`ring_refinement_scalar_word` are retained; the latter is still an unproved theorem in its
own module, not a hole introduced by this delivery.

Validation: the repaired module compiled cleanly through `lcompile.py` in 13.5 seconds,
with the existing heartbeat and time limits. The delivered Lean file contains zero `sorry`
tokens and no lines longer than 100 characters.

## No longer needed

None. Both imports and both proof-dependency nodes remain needed. No modules or nodes are
withdrawn. Mathlib's explicit isomorphism cancellation replaces only an implicit search for
a `Mono` instance.

## Where the brief, the DAG or earlier work was wrong

The shared snapshot's saved build error reported only failed imports, and its local queue had
no item row. Reading the current server queue and build-error file revealed the actual repair:
line 168 failed to synthesize `Mono` for the composite, reaching the deterministic typeclass
heartbeat limit; line 170 then reported no goals. This is a proof-elaboration defect, not an
unproved mathematical obligation. No statement or definition repair is needed.

The item node and its two dependency nodes were read, together with their declarations and the
compatibility unit. The proof route remains the specified full-subcategory lift, faithful
shift reflection, and scalar-word conjugation. The replacement cancellation works for any
isomorphisms, including identity refinements and zero objects, with no added hypotheses.

For this rework, the item module was restored from its quarantine copy and the same repair was
reapplied. Its declaration, statement, imports, and DAG attachment are preserved. The restored
module compiled cleanly in 14.2 seconds against the current published build, with zero `sorry`
tokens and no overlong lines.


## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstructibleRingLeftRefinement": "a3ee13aa6ef575499238cf72939b2ca2e92b534f"}, "results": {}, "time": "2026-10-28T06:05:20+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
