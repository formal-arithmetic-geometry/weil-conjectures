## What changed

Proved `WeilConjectures.publishedSystemTransportedTensor_eq_of_flat_normalized` in
`Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization`. The proof imports
`Sheaf.Algebra.Homology.CochainTensorModelRigidity` privately, applies faithful restriction
to flat-term K-flat pairs, compares the assumed rectangle with the canonical comparison's
existing defining rectangle, and cancels two explicit map isomorphisms. The cancellation argument is a fully proved private helper with its comparison
isomorphisms abstract, avoiding expensive kernel unfolding of the concrete choices.
All existing declaration signatures, definitions, public imports, attributes and
previously proved bodies are preserved. A scoped unused-variable linter option on
the descent theorem retains the original names of its intentionally unused bound
flatness witnesses inside the hypothesis type.

Updated the descent node's proof and proof dependencies to record this direct argument.
Expanded both theorem docstrings with their proofs in words so the remaining hole
can be taken over without reconstructing the ambient normalization plan.
No other existing module or another module's node is changed. No change record is needed.

## Proved and sorry left

Closed one of the item's two original holes:
`WeilConjectures.publishedSystemTransportedTensor_eq_of_flat_normalized`
(node `lem-sf-published-system-tensor-identification-representative-descent`).
This is a proof from existing declarations, not a decomposition. Zero holes are added,
and no statements are split off.

One existing hole remains unchanged:
`WeilConjectures.publishedSystemTransportedTensor_normalized_flat`
(node `lem-sf-published-system-tensor-identification-representative-flat`).
Its unresolved step identifies the ambient inverse chain map, via the equality of the
chosen inverse-image presentations and their adjunction units, with the inverse of the
specified sequence cochain comparison. The ambient model's derived equation alone does
not identify those chain maps. This delivery does not relocate that obligation.

Validation: lcompile.py compiled the proof with profiling in 20.0 seconds. The
profiling options are removed in the final source; deliver3.py runs the required
compilation, declaration and axiom checks. The argument imposes no additional assumptions
on schemes or complexes. Zero complexes and the identity morphism are included, since
only components of given isomorphisms are cancelled. No boundedness or transition
invertibility is used.

## No longer needed

No imports are removed and no module is withdrawn.
For the descent theorem specifically, the proof no longer invokes
`lem-sf-system-pullback-tensor-normalization` or the flat normalization theorem
`lem-sf-published-system-tensor-identification-representative-flat` as a lemma.
Its hypothesis already supplies all flat representative rectangles, and faithful
restriction suffices. Its proof dependencies are now exactly
`lem-sf-cochain-tensor-model-rigidity` and
`lem-pur-coherent-derived-pullback-tensor`.
The flat normalization node remains needed by the unchanged proof of
`publishedSystemTransportedTensor_normalized`; no global pruning is claimed.
The blueprint unit `sk-rem-sf-pf-done` has no realized statement or steps to bypass.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The previous descent plan described
inverse representative equations and tensor-comparison uniqueness, but its displayed
hypothesis supplies forward equations. Comparing those equations directly and applying
cochain tensor rigidity closes this hole without converting to the inverse-model API.
The first compiler check could not infer that tensor applied to `Prod.mkHom` is mono;
explicit `Functor.mapIso` and `Iso.prod` supply the required invertibility and avoid
expensive instance search. The private cancellation helper abstracts
both comparisons so its kernel check does not expand the concrete ambient and
canonical choices. The public theorem composes the two forward rectangles and
passes their equality to that helper. Profiling options are removed from the
delivered file.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization": "c0c634ff20eed4e8031d67040a10ef97ba15294a"}, "results": {"Sheaf.SixFunctors.PublishedSystemTensorIdentification": {"hash": "3c612b614772329438b649508249ab2fbe797b1c", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T07:54:49+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
