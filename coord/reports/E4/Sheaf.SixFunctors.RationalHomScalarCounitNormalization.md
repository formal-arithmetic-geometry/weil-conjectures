## What changed

Replaced the proof hole in `normalizedCounit_localized_integral` without changing its
statement or the definition `normalizedCounit`. Two proved private helpers carry the
actual work: `normalizedCounit_integral` identifies the rational composite with the
localization of integral braiding followed by integral evaluation;
`integralCounit_normalized` derives the integral evaluation formula from a tensor square,
inverse-transpose normalization, and counit preservation by uniqueness of left adjoints.
The existing final theorem `homIdentification_counit_normalized` is unchanged.

Added proof-only imports of `NormalizedRationalEvaluationNaturality` (with `all`, to use
its already proved private normalization lemmas) and the new
`OrdinaryCompletedTensorAdjointSquare` module. The latter states a genuine earlier step:
a comparison of integral tensor maps on arbitrary constructible inputs, with no rational
category, permitted-Hom hypothesis, HomIdentification, or evaluation in its conclusion.
No other existing Lean file, public signature, definition, instance, or public import changed.

## Proved and sorry left

One original hole is reduced:
`WeilConjectures.RationalOperations.normalizedCounit_localized_integral`
(node `lem-sf-rational-hom-counit-normalized-localized-integral`). The item module has
zero remaining holes. The rational descent calculation and the integral categorical
counit argument are complete Lean proofs.

One hole is added:
`WeilConjectures.RationalOperations.ordinaryCompletedTensor_adjoint_square`
(node `lem-sf-ordinary-completed-tensor-adjoint-square`), in its own new module.
Its proof is exactly `by sorry`. This is a decomposition, not a net hole closure:
one hole closed, one added. No complete proof of the new integral tensor square is claimed.

The new square is strictly a tensor-normalization step: it compares the canonical
left-adjoint comparison followed by completion with completion followed by braiding.
The item specializes it to an internal Hom, postcomposes with integral evaluation,
uses two independent closed-adjunction identities, cancels completion, and then
localizes. Thus the remaining theorem is not the original obligation under another name.

The development compile checks both files individually in import order. Profiling found
that making `Scheme.residueField` and `HasDerivedCategory.standard` locally irreducible
keeps the item comfortably within the 60-second limit; no definition was changed.
The final delivery tool supplies the independent compile and axiom probes.

## No longer needed

None. No import, existing dependency node, or module is pruned or withdrawn.
The original definition and raw-localization dependencies remain necessary.
The unit record has no realized statement/steps to replace; this reduction stays within
the original normalization and localization route.

## Where the brief, the DAG or earlier work was wrong

The previous node plan treated the equality between the supplied ordinary completion
presentation and the canonical closed tensor evaluation as an expansion. The two
presentations are independently normalized, so this requires a tensor comparison square.
The rational evaluation localization identity is already proved in a private helper;
`import all` permits its reuse without changing that module or its public interface.
The new square isolates the actual remaining normalization instead of splitting off the
rational counit statement again.

Checked the queue, rework/build-error records, current E4 return notice, and definition
owners. The queue assigns a proof item, not a repair. No current item-specific build error
or rework row was present. The old general sync notice requires no item source changes.

For the new square, zero objects and empty schemes use the same tensor and localization
universal properties; no nonzero or nonempty premise is needed. Its arbitrary completion
is pinned on all good representatives by its existing `representative` field. Mathlib
searches found the generic adjoint-uniqueness counit law, which is used directly; none
supplies the project-specific quotient/Roos normalization square.

## New nodes

`lem-sf-ordinary-completed-tensor-adjoint-square` owns the single new theorem in
`Sheaf.SixFunctors.OrdinaryCompletedTensorAdjointSquare`. Its complete proof plan compares
normalized ordinary signed evaluation on K-flat representatives, compares the two Roos
coordinates, and descends the tensor equality. The source is the integral normalization
step in the current blueprint rational-Verdier proof, with the existing tensor-completion
and coefficient-calculus declarations named in the node. There are no change records
because no existing interface or other module is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.OrdinaryCompletedTensorAdjointSquare": "128e117bd7649866b881e9856183626fcfc0a8bc", "Sheaf.SixFunctors.RationalHomScalarCounitNormalization": "d3505fa06a0f8c5bf8d8d49c61fb8580dc606c67"}, "results": {"Sheaf.SixFunctors.RationalHomScalarEvaluationCore": {"hash": "85cd7fc86cc0d6b1a77d8a945304e39e1a3616d4", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T12:05:14+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
