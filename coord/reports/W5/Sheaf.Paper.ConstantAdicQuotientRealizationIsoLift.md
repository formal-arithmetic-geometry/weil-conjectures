## What changed

The target theorem now has a complete Lean proof.  It unwraps the supplied
realized isomorphism, applies the new morphism-lift statement, and then applies
the new map-level reflection statement to prove that the lifted morphism is an
isomorphism.  The two hard point-stalk arguments are recorded as separate
strictly smaller stage-3 statements.

## Proved and sorry left

Proved: `AlgebraicGeometry.Scheme.constantAdicQuotientRealization_iso_lift`.

Sorry left in the two split-off statements:

- `AlgebraicGeometry.Scheme.constantAdicQuotientRealization_iso_hom_lift`:
  lifts a realized isomorphism to an algebraic morphism with the same image.
- `AlgebraicGeometry.Scheme.constantAdicQuotientRealization_reflects_iso_of_map`:
  reflects `IsIso` from a realized map to its algebraic source map.

## No longer needed

No imports were removed.  The original direct dependencies are used by the
split statements: scalar comparison supports both, and the generic constant
realization reflection declaration supports the map-level reflection split.
No additional declared nodes or modules became unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original node presented fullness and reflection as one extraction step, but
the library has no theorem lifting an arbitrary realized isomorphism.  The
target therefore could not be proved by the available reflection declaration,
which only accepts a morphism already present.  The route was corrected by
splitting the argument into the fullness statement and the map-level reflection
statement, then composing them in the target.

## New nodes

- `lem-weil-pbc-constant-adic-quotient-realization-iso-hom-lift`
- `lem-weil-pbc-constant-adic-quotient-realization-reflects-iso-of-map`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantAdicQuotientRealizationIsoHomLift": "4e6c007bf17d17f3279ef806cf5d20f061999fbf", "Sheaf.Paper.ConstantAdicQuotientRealizationIsoLift": "d6e067f4055721fccc4bf4439f2e0098aa320590", "Sheaf.Paper.ConstantAdicQuotientRealizationReflectsIsoOfMap": "997c665490f93278d57903ccbf0ac2b94f01dc45"}, "results": {}, "time": "2026-10-28T10:50:50+0800", "transitive": 0, "version": 1}
```

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
