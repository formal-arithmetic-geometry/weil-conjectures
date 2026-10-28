## What changed

Completed `WeilConjectures.RationalVerdier.localized_extension_composition` in
`Sheaf.SixFunctors.RationalVerdierLocalizedComposition`, with its original signature.
The proof cancels the dual inverse associator in the beta clause of the supplied
integral `CompositionConclusion`, restricts the resulting equation to integral
constructible objects, and applies the target localization functor. It identifies
the rational factors with these localized integral factors using the supplied
three comparison normalizations and associator normalization, `Datum.objects`,
`Datum.pure` at coefficient one, and the scalar-extension object and map formulas.
Validation: the final module compiles cleanly through `lcompile.py` in 14.5 seconds.
Its existing theorem signature was checked unchanged verbatim, all Lean lines are
at most 100 characters, and the delivered Lean contains zero `sorry` tokens.

Three proved private helpers transport maps and natural-transformation components
through heterogeneous endpoint equalities. Local irreducibility attributes keep
unrelated large internal-Hom constructions out of elaboration.

Updated the item's DAG proof, proof dependencies, and proof origin to record these
steps. No statements, definitions, public imports, or other modules were changed.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.RationalVerdier.localized_extension_composition`
(node `lem-coef-rational-verdier-localized-composition`).
Holes closed: 1. Holes added: 0. Sorries remaining in delivered modules: 0.
No split-off statements were introduced. The proof assumes the original integral
composition package exactly as the theorem's signature requires.

## No longer needed

Removed the unused private import
`Sheaf.SixFunctors.RationalVerdierIntegralCocycle`. This theorem does not construct
its integral cocycle; its caller supplies `hcomp`, so the cocycle theorem is not
needed by this module. Its parent still uses that theorem, so the module is not
withdrawn or claimed to be globally pruned.

The proof no longer cites `lem-coef-rational-verdier-composition-normalization` or
`lem-coef-integral-finite-extension` as theorem dependencies: their relevant
normalization and composition equations are hypotheses. The actual defining
packages are recorded as `def-sf-integral-finite-extension-core` and
`def-sf-rational-verdier-data`, together with
`def-weil-rationalization-karoubi`. These other modules/nodes remain available to
other users and are not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old proof plan described extension from pure localized tensors by additivity.
Here every map being compared is the localization of a specific integral arrow;
the coefficient-one formulas suffice. Associator cancellation must be performed
before localization, and the proof explicitly tracks each endpoint equality.
The source composition clause in the current blueprint is preserved. The unit's
`realized` lists are empty, and no unit-level route was bypassed.

Searches: LeanFinder returned generic localization/composition infrastructure;
Loogle did not resolve the unqualified `Functor.map_comp` query. The grep search
found Mathlib's `CategoryTheory.heq_comp`; source searches found the project's
scalar localization formulas and the integral beta conjunct. No exact existing
project theorem for this transport step was found.

The argument treats zero and torsion objects, empty schemes, and identity
embeddings uniformly: it uses only functoriality, isomorphism cancellation, and
the stated normalization formulas, with no faithfulness or nonvanishing premise.

Process note: initial inspection mistakenly included read-only git/history
commands in the shared repository and a search broader than the permitted
project directories. These commands made no project edits. Subsequent inspection
was restricted to the named project paths; all edits are in the assigned sandbox.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierLocalizedComposition": "6b2de6edf06c64d7d2ee7481e5581ca65f531c10"}, "results": {"Sheaf.SixFunctors.RationalVerdierCompositionEquation": {"hash": "c6a378cee2397dc18299c71361d6a0f6abb6366f", "status": "OK"}}, "seconds": 130, "time": "2026-10-28T12:05:56+0800", "transitive": 0, "version": 1}
```

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
