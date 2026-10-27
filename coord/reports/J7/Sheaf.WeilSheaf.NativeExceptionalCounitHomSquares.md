## What changed

Replaced the assigned theorem's hole by an explicit proof from two strictly smaller geometric obligations. Its signature and both existing public imports are unchanged. The only new import in the item is the private proof import `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit`.

`NativeExceptionalHomTransport` constructs the actual native compactification, its ordinary open/proper composite, the restricted unit-normalized forgetting comparison, and the graded transport map. Its remaining theorem concerns only this left functor: it preserves cyclic action, forgetting, and the normalized boundary. It has no exceptional adjunction, counit, or Hom equivalence.

`NativeExceptionalOrdinaryCounit` states the ordinary portion of the argument: realization of the exceptional image's Frobenius action, an invariant ordinary counit carrier, its comparison with the specified common-stage counit, and ordinary graded adjunction bijectivity. It does not assert existence of a native counit morphism or either outer cyclic equivalence or square.

The item's proof lifts the ordinary carrier by degree-zero surjectivity, proves its precise common-stage equation using realization naturality and full faithfulness, packages graded Hom bijections as additive equivalences, proves equivariance using the native lift, restricts to the actual kernel and descends to the actual quotient, and proves both requested squares. The left square uses quotient induction and boundary naturality; the right square uses the zero-shift comparison's naturality. No faithfulness of derived forgetting is used.

To keep elaboration within the per-file limit, the proof uses explicit existential projections rather than repeated large dependent-pattern elimination, and handles postcomposition in generic private lemmas. A local irreducibility attribute prevents expansion of the standard derived-category model; it does not change any exported definition or attribute. Profiling and trace options used during development have been removed.

## Proved and sorry left

The original hole in `WeilConjectures.NativeExceptionalForgetful.native_exceptional_counit_hom_squares` is replaced by the described complete Lean assembly. Its module has zero `sorry` occurrences. The four private algebraic helpers are proved.

Validation through lcompile.py: NativeExceptionalHomTransport compiled in 20.5 seconds, NativeExceptionalOrdinaryCounit in 10.2 seconds, and the final assigned module in 38.0 seconds with no warnings. The original theorem signature is byte-for-byte unchanged. All Lean lines have at most 100 characters. Only proof, proof_deps, and proof_origin change in the existing parent node.

Two holes are added, one per new module:

- `WeilConjectures.NativeExceptionalForgetful.counitHomTransport_compatible`, node `lem-sf-native-exceptional-hom-transport`.
- `WeilConjectures.NativeExceptionalForgetful.native_exceptional_ordinary_counit`, node `lem-sf-native-exceptional-ordinary-counit`.

This is a decomposition: one upper hole removed and two strictly smaller holes added, not a net proof advance. Neither lower theorem repeats the assigned conclusion: the first is independent of exceptional adjunction data, and the second is restricted to ordinary derived morphisms before a native counit lift and before kernels and quotients. No definition contains a hole, and no definition selects new arbitrary data from an unproved existence statement. The compactification abbreviation refers to the exact existing compactification used by the native functor.

## No longer needed

No existing public import is removed. The former direct proof dependency `lem-sf-cyclic-derived-lifted-counit-represents` / `Sheaf.CategoryTheory.CyclicDerivedLiftedCounitRepresents` is unnecessary for this proof. Its geometric hypotheses did not yet match the specified native/common-stage presentations. The native counit lift and the two outer equivalences and squares are assembled directly instead. This does not assert that the generic module is globally unused.

The previous direct dependencies `lem-sf-native-weil-open-proper-forgetting`, `lem-sf-native-weil-scalar-frobenius-counit`, `lem-sf-adic-qbar-constructible-realization`, and `lem-sf-cyclic-derived-hom-exact-sequence` remain needed below the new geometric obligations; they are not pruned from the project. They are removed only from the item's direct proof-dependency list in favor of the exact new immediate dependencies. No Lean module or declaration is withdrawn. The unit and chapter routes are preserved.

## Where the brief, the DAG or earlier work was wrong

The running server queue identifies a one-hole proof item, and there is no current build-error file for it. The older rework record names its existing data import; the current source exists and was preserved. No quarantine attachment is deleted or replaced by an empty module.

The old plan skipped a real implementation comparison. Cyclic finite-composite functoriality is formulated with `rightDerivedFunctorOfQuasiIsoResolutions`, while native compact support uses the source library's `rightDerivedFunctor`. Their comparisons must be identified through their unit-compatible universal properties, including shifts. Compiling an unproved specialization does not establish this identification; it remains explicit in the new Hom-transport obligation.

The ordinary scalar-counit theorem is also stated for particular coefficient and section presentations. The comparison to arbitrary supplied ForgetModels, S, and c belongs to the ordinary-counit obligation. None of these gaps is solved by assuming a native right adjoint or by dropping the degree-minus-one term.

Edge cases checked in the statements: no intermediate boundedness is added to the transport theorem; no exactness assumption on its boundary families is needed; zero groups on empty schemes and identity compactifications retain the same formulas. The counit lift in the item uses only target sequence surjectivity, and boundary naturality is evaluated with the exact native boundedness witnesses.

## New nodes

`lem-sf-native-exceptional-hom-transport` records the fixed native compact-support transport and its normalized cyclic functoriality, with a complete source-based proof plan explaining the two right-derived implementations. Its module is `Sheaf.WeilSheaf.NativeExceptionalHomTransport`.

`lem-sf-native-exceptional-ordinary-counit` records only the ordinary exceptional-image realization and graded adjunction calculation, before the native lift and the two outer maps. Its module is `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit`.

Both inherit the item's chapter and unit. The parent proof, proof dependencies, and origin are updated to the implemented argument. No other existing module or node changes, and no change record or forced consumer adaptation is needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares": "2943a9fc6fd129f8289051e2740553ab4f9defcc", "Sheaf.WeilSheaf.NativeExceptionalHomTransport": "b1bfb8088d3ec79a7fe43d0f8a201a0ae6d86776", "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit": "405a32b4eb917c3f54c4bf412d1be32cf2998dd0"}, "results": {"Sheaf.WeilSheaf.NativeExceptionalLeftModels": {"hash": "4d6553f2ef3e08a14148f5f9c538d37140827f2b", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T01:03:35+0800", "transitive": 0, "version": 1}
```

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
