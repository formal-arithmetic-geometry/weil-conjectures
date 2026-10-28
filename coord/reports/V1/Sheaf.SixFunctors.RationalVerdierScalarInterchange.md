## What changed

Replaced the original hole in `WeilConjectures.RationalVerdier.integral_scalar_interchange`
by rewriting the two interchanges as canonical integral braidings, then applying the
existing `WeilConjectures.integralBraidingScalarExtensionSquare`. Its signature and
the existing rational `scalar_interchange` proof stay identical.

Proved the new one-datum theorem `completedInterchange_eq_integralBraiding` in Lean.
The ambient completed swap is an explicit transport of the strict-system braiding.
Adjunction-counit naturality proves its canonical reduction normalization. The product
localization universal property reduces the natural-transformation identity to good
cochain representatives. There the supplied symmetry and completion representative
formulas, with the remaining chain lemma, prove the square. Cancellation of the
invertible completion map then proves the constructible identity. The supplied
ambient naturality hypothesis is used to form the natural transformation.

The remaining chain lemma is `completion_signed_representative`. It concerns one
coefficient field and two flat-term K-flat complexes with a prescribed Koszul chain
map. It has no scalar embedding, Verdier datum, naturality premise, constructibility
premise or inverse completion map. Its docstring explains the quotient-coordinate,
zero shifted-coordinate, and strict tensor-model calculation. The zero-complex and
empty-site cases obey those same coordinate equations.

All new definitions are concrete constructions; no existing definition, statement,
attribute or public import was changed. Only proof imports were added to the item.

## Proved and sorry left

Original holes: 1. Closed `WeilConjectures.RationalVerdier.integral_scalar_interchange`.
Original item holes remaining: 0. Added holes: 1, exactly
`WeilConjectures.RationalVerdier.completion_signed_representative` in
`Sheaf.SixFunctors.RationalVerdierCompletionSignedRepresentative`.
`completedInterchange_eq_integralBraiding` is proved, with no local holes.
This is a decomposition, with net hole change zero, rather than a claim of a
sorry-free result. The existing canonical braiding scalar square is an allowed
stated dependency and retains its own upstream proof obligations.

Validation: compiled the new modules and the item in import order using lcompile.py.
The canonicalization proof uses local reducibility annotations for ordinary wrapper
definitions and keeps respectTransparency enabled. No shared source module changed.

## No longer needed

No existing module is withdrawn, and no existing import was removed. The item no
longer directly needs `lem-pc-kflat-resolution`,
`lem-sf-cochain-tensor-model-rigidity`, `def-sf-integral-verdier-models`,
`lem-fix-constructible-tensor-completion`,
`lem-pur-normalized-integral-scalar-tensor-descent` or
`def-sf-rational-verdier-data` as separate proof steps: the canonicalization and
canonical scalar-square dependencies replace that route. Some remain needed
transitively for those dependencies; no claim of whole-library pruning is made.
The rationalization and pairing-calculus dependencies remain in the DAG because
this node also realizes the already proved rational `scalar_interchange` theorem.
The unit route is preserved; its realized statement and steps are empty.

## Where the brief, the DAG or earlier work was wrong

The original plan expanded a scalar-compatible completion square although an
existing canonical integral braiding scalar-extension theorem handles that part.
The actual missing calculation is its compatibility with the fixed completion
chain map. The delivery proves the localization, normalization and invertible
conjugation surrounding that calculation, rather than merely renaming the scalar
interchange obligation. The previous generic canonicalization split is now a
proved theorem; only its explicit chain-representative step remains open.

Current queue entry assigns a one-hole proof route. There is no current build-error
file for the item. The current source and dependencies, including the normalized
completion and good-complex localization, were used for the compiles.

## New nodes

- `new-lem-coef-rational-verdier-completed-interchange-canonical`: proved one-datum
  canonicalization, including reduction normalization, localization and cancellation.
- `lem-coef-rational-verdier-completion-signed-representative`: remaining one-field
  signed completion equation on good cochain representatives, together with the
  explicit transported ambient swap. Its Lean statement, source, proof in words,
  dependencies and searches are recorded in its node.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierCompletedInterchangeCanonical": "6b558637359e00f66eaca1d59cc74ba03eb4baac", "Sheaf.SixFunctors.RationalVerdierCompletionSignedRepresentative": "91dbddac904b0df75b6592d8c109e2a226de8e77", "Sheaf.SixFunctors.RationalVerdierScalarInterchange": "77edc7f5b830e0abc12e2f63c7596386b0e8a266"}, "results": {}, "time": "2026-10-28T09:57:48+0800", "transitive": 0, "version": 1}
```

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
