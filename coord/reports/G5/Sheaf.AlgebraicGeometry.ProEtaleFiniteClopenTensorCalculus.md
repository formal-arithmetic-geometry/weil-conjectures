## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.finite_clopen_scalar_calculus`
for arbitrary coefficient-extension presentations and their prescribed normalizations.
The proof applies the existing scalar comparison descent, model, unit and coherence
interfaces. Four proved private quotient lemmas identify their cochain representative
square with the statement's homotopy-category square. Composition is the recorded
coherence equation after expanding `scalarComposite`.

Reuse the canonical scalar module, ring-restriction, module-restriction and standard
localization aliases. Their old and new data are definitionally equal. The change
record lists downstream uses and explains why the statements retain their meanings.
The earlier derived-product proof and its private consumer API are retained, with
local sealing of the large localization data and sealing of the standard localization core.

Verification: the scalar implementation compiled as a complete module in the scratch
probe `ScalarCanonicalFinalProbe.lean` (49.5 seconds). The localization-core-sealed variant compiled cleanly in 51.4 seconds. The actual item-path compile is being rerun after this final source copy. A separate definitional-equality probe compiled in 14.5 seconds. The final
item-path compile and preflight are performed by `deliver3.py`; this report does not
claim that separately timed-out full tensor candidates were verified.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.finite_clopen_scalar_calculus`.

One original hole remains:
`AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.finite_clopen_tensor_calculus`.
Its original source and complete proof in words remain in the declaration's docstring
and DAG node. No hole was added, no statement was split off, and no definition contains
`sorry`. The already proved `finite_clopen_derived_calculus` is retained.

## No longer needed

The scalar proof does not use the wrapper node
`lem-pur-clopen-derived-scalar-compositor` or its module
`Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarCompositor`: its existential choice
of presentations does not directly fit the universal quantifiers here. Use its lower
comparison descent, model-properties, unit-normalization and coherence declarations
instead. Remove that wrapper from this node's proof dependencies; retain its public
declarations and all other consumers.

No existing import is removed and no module is withdrawn. In particular, retain
`derivedPi_isEquivalence`, `moduleGluing` and `piPreadditive`: the strict-tower and
constructibility consumers use these proved private helpers through `import all`.
The original tensor route still needs both total-tensor detection and monoidal descent.
No unit statement or required unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The scalar-compositor dependency concludes existence of chosen presentations, whereas
this item's theorem quantifies over arbitrary presentations. Its lower declarations
already give the needed universal version, so the proof applies them directly.

The monoidal-descent dependency's representative square is only normalized on flat-term
K-flat complexes; this item's tensor theorem asks for arbitrary K-flat complexes.
A naturality argument along flat-term K-flat resolutions is therefore needed in addition
to the listed assembly. That argument was written and its normalization helper compiled,
but the combined full-module proof still exceeded the 60-second compile limit. It is
not included as an unverified proof or a new hole in this delivery. No statement is
believed false, and no hypothesis or conclusion was changed.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
