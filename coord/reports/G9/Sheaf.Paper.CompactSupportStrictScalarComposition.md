## What changed

Reduced `WeilConjectures.PurStrictScalar.compactSupportScalarLimitComposition` to the
existing strict composition theorem and two independent coherence statements about
normalized tensor/limit comparisons. The categorical combination is a complete Lean
proof: postcompose with the cofinal map, move the support associator and the strict
arrow by naturality, cancel the two intermediate cofinal inverses, and apply strict
composition and horizontal tensor coherence.

Proved the arithmetic cofinal composition law privately, from equality of the
actual index functors, ordinary `limit.pre_pre`, and the adopted proved theorem
`Functor.rightDerivedPullback_comp`. No finite-evaluation faithfulness is used.
The two new proof imports contain one public coherence theorem each. All original
public declarations, definitions, statements and imports are preserved.

Validation: both new modules compiled without warnings through `lcompile.py --all`.
The final item compiled without errors or warnings through `lcompile.py` in 49.9 s.
JSON parsing and the 100-character line-width checks pass; temporary profiling
options were removed before the final compile.

## Proved and sorry left

This is a decomposition, not a net proof gain: one existing hole is closed and
two strictly smaller holes are added. The item started with five holes and now
contains four; the delivery contains six holes in total.

Closed in the item: `WeilConjectures.PurStrictScalar.compactSupportScalarLimitComposition`.
Its proof uses the unchanged strict-composition declaration, which remains open.
The private `scalarLimitRestriction_composition` is proved without holes.

Unchanged holes, all belonging to `lem-pur-compact-support-strict-scalar-composition`:

- `WeilConjectures.PurStrictScalar.compositionProper`;
- `WeilConjectures.PurStrictScalar.compositionOpen`;
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarComposition`;
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarIdentity`.

Added holes:

- `WeilConjectures.PurStrictScalar.scalarLimitTensor_composition`, node
  `lem-pur-scalar-limit-tensor-composition`;
- `WeilConjectures.PurStrictScalar.scalarLimitTensor_restriction`, node
  `lem-pur-scalar-limit-tensor-restriction`.

These are geometry-independent parts of auxiliary Step 7, applying to arbitrary
unbounded towers. They mention no compactification, support functor, scalar support
arrow, or finite-Tor input; neither restates the compact-support equation.
Their edge cases include the zero tower, identity coefficient embeddings, and
arithmetic selection by one. Their docstrings give the source and complete proof
in words using the existing coordinate coherence and normalization declarations.

## No longer needed

None. No imports, declarations, nodes or modules are withdrawn. The four unchanged
holes still need the original plan. The new steps isolate the canonical comparison
coherence needed to transport the strict equation to limits; they do not bypass a
blueprint unit or prune a source-library declaration.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The original Step 7 states coherence for
explicit Roos cochain maps, whereas the item uses `scalarLimitTensor` and
`scalarLimitRestriction`, defined by normalized derived-composition comparisons.
The two new lemmas isolate that identification, with the actual localization
factors and ordinary associators. Arithmetic cofinal composition itself needs no
new unproved result: it follows from the adopted right-derived pullback composition
law and `limit.pre_pre`.

## New nodes

`lem-pur-scalar-limit-tensor-composition` states horizontal coherence for the
specified `scalarLimitTensor` and any ordinary scalar-extension isomorphism.
Its module is `Sheaf.Paper.ScalarLimitTensorComposition`.

`lem-pur-scalar-limit-tensor-restriction` states compatibility of the specified
`scalarLimitTensor` with the arithmetic cone restriction map and the exact
localization of the identity tensor/selection square. Its module is
`Sheaf.Paper.ScalarLimitTensorRestriction`.

Both nodes retain the parent chapter and unit, have independent sources and proof
steps, and depend only on already declared theory below the parent. No definition
or existing statement changes, so no change record or consumer adaptation is needed.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
