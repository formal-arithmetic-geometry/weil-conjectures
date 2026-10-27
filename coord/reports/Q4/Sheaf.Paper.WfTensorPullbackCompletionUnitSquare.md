## What changed

The item theorem retains its statement. Its derived square follows from the defining unit
characterization of `wfPullbackCompletion` and naturality of `wfCompletionUnit`. Its strict
square combines a uniquely normalized completed-constant comparison with transport of the
augmented Koszul product/fiber; functoriality of `DerivedCategory.Q` gives the displayed
localization equation.

The shared interface is relocated to `Sheaf.Paper.WfTensorUnitSquareData`, publicly reexported
by the item, so the two separate mathematical results can use it without an import cycle.
All declaration names and mathematical bodies are retained. The total tensor and alpha use
explicit definition boundaries; beta's intermediate maps have explicit types to prevent
uncontrolled elaboration of the same total tensor objects. The change record is
`coord/changes/wf-tensor-unit-square-interface.md`, including the current downstream users.
No file under `lean/WeilConjectures/` is changed.

## Proved and sorry left

Closed the item's one hole in
`WeilConjectures.wfTensorPullbackCompletionUnitSquare`, by a complete composition proof.
Proved the new separate coefficient result
`WeilConjectures.WfTensorUnitSquare.completedConstantPullback_normalized`
(node `lem-wf-completed-constant-pullback-normalization`). Its proof compiles without
admissions. The private derived-square argument is complete from the existing completion
comparison's unit equation and naturality.

One new hole remains:
`WeilConjectures.WfTensorUnitSquare.normalizedKoszulFiber_unit_transport`
(node `lem-wf-normalized-koszul-fiber-unit-transport`). Its proof is exactly `by sorry`.
There are no holes in definitions or private declarations. Thus one original hole is closed
and one strictly separate hole is added: this is a decomposition, with net hole reduction
zero, not a claim that the strict chain calculation is finished. The coefficient comparison,
its uniqueness, the derived square and the combination/localization argument are proved.

A full strict-transport draft was attempted and compiled repeatedly. The remaining formal
work is totalization naturality, tensor-unitor normalization, product comparison instances,
and the signed cone coordinate equations. The retained theorem is the chain-level part of
the source argument conditional on an arbitrary normalized k, without coefficient existence,
uniqueness, derived comparison or localization conclusions. No partial admitted proof is
retained in the delivered Lean files.

Final `lcompile.py --all` verification compiled all four delivered modules successfully:
data 31.8 s, constant normalization 29.0 s, strict transport statement 28.2 s,
and the item theorem 27.1 s. The first preflight caught a node-signature metadata mismatch;
that metadata and the two newly listed consumer records were corrected.

## No longer needed

The private import `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage` is removed.
The proof uses the ordinary ringed pullback and its adjunction, rather than the separate
sectionwise inverse-image model. The corresponding direct dependency
`lem-weil-proetale-isomorphism-inverse-image` is replaced by the immersion limit-preservation
result for product preservation. The canonical tensor-pullback results remain necessary.
The original public imports are reexported through the data module; they are not pruned.
No module is withdrawn, and no unused adopted-source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The original plan suppresses the generator normalization of completed constants. Its existing
Lean predicate quantifies over all constant modules and site objects, so the proof needs the
constant-module/global-sections adjunction and the scalar direct-image square. The new
constant-normalization result states and proves precisely that part. The strict transport
calculation works for arbitrary complexes and any normalized comparison; flatness and the
chosen derived representatives are only needed by the surrounding application.

The Lean tower uses positive exponent `m + 1`; the informal display with exponent `m` is read
with the corresponding positive-index convention. The existing Lean definitions are retained.
The unit's statement and realized route are unchanged.

## New nodes

`def-wf-tensor-unit-square-data` records the existing coefficient, tensor, product, fiber and
normalization definitions in their shared interface module. It introduces no additional
mathematical data or admission.

`lem-wf-completed-constant-pullback-normalization` isolates the unique generator-normalized
constant comparison, obtained by composing adjunctions and transporting global sections
through the scalar square. It is the coefficient step of the original source argument.

`lem-wf-normalized-koszul-fiber-unit-transport` isolates transport of the augmented Koszul
fiber for an arbitrary normalized coefficient comparison and arbitrary complexes. The level
unit follows on pure tensors and totalization inclusions; product projections and the
functorial signed cone give the actual `(u,0)` unit equation. The source is the level/product/
fiber calculation in the original node and the latest blueprint's equivariance sentence.
The recorded searches found generic adjunction and tensor APIs, not either normalized result.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
