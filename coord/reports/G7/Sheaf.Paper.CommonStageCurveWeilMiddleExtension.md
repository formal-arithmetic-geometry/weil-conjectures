## What changed

Prove `WeilConjectures.qbarAffineArithmeticGeometry` in
`Sheaf.Paper.CommonStageCurveWeilMiddleExtension`. Finite type over the finite
field gives local Noetherianity, and the affine structure map gives compactness.
Together these give Noetherianity. `fourierBaseCharacteristic` supplies
characteristic p on the base field. The affine zero section proves that the
ring of global functions is nontrivial, and the ring map from the base field
to global functions transfers characteristic p.

All existing public signatures, definitions, docstrings and imports stay
unchanged. No helper declaration is added. The existing node
`def-wf-middle-extension` records this proof and its dependency on the already
proved Fourier affine-geometry interface (`def-fd-transform`).

The zero-section argument checks nontriviality explicitly; it does not infer
that every algebra over a characteristic-p field has characteristic exactly p
without a nontriviality argument. The finite field is Noetherian independently
of its cardinality, and the characteristic calculation uses its recorded p^a
cardinality through the existing `fourierBaseCharacteristic` theorem.

## Proved and sorry left

One of four original holes is closed:
`WeilConjectures.qbarAffineArithmeticGeometry`.

Three original holes remain unchanged, all attached to `def-wf-middle-extension`:

- `WeilConjectures.qbarCurveWeilPull_isLeftAdjoint`;
- `WeilConjectures.qbarCurveWeilOrdinaryPushforward_forget`;
- `WeilConjectures.qbarAffineWeilShift_forget`.

No holes are added or split off. Every remaining hole retains its original
source and complete proof in words in the declaration docstring. No partial
proof, new statement, axiom, or hollow definition is delivered.

## No longer needed

None. Both original public imports are still needed by statements and
definitions. No module is withdrawn and no target or unit route is bypassed.
The original node had no proof-dependency list or proof steps to prune.

## Where the brief, the DAG or earlier work was wrong

The definition node has an empty original proof plan, while its Lean attachment
contains four named postponed proof obligations. This delivery records the
completed geometry proof without changing the mathematical definition.

The generic `IsoAlgebra.mapOfNatIsoAdjunction` appears suitable for the two
ordinary Weil-heart obligations, applied to `qbarCurveOrdinaryAdjunction` and
heart Frobenius equivalences. I implemented private carrier-pair equivalences
and the mate adjunction, but the necessary comparison with `zlWeilPull` repeatedly
hit elaboration heartbeats or the 60-second file limit while reducing the nested
full-subcategory and Frobenius-square definitions. Profiling, explicit component
maps, folded pullback definitions and projection simplifications did not produce
a compiling full comparison. Those unfinished changes are excluded from this
packet. No compile limit or launcher script was changed.

The remaining shift comparison needs the completed trivial-character line's
coefficient-unit comparison and the signed common-stage tensor/shift comparison;
the geometric affine-line proof does not supply it.

An initial remote compile failed before Lean started because its temporary
filesystem was full. A retry reached Lean; this was transient.

Validation: the delivered module compiled through `lcompile.py` with exit code 0,
no diagnostics, in 14.9 seconds. Its only textual holes are the three named
unchanged obligations above. The proof uses no new import or public interface.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
