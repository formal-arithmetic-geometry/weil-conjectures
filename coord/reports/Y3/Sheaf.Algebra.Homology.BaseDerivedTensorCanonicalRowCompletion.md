## What changed

Proved `ModuleCat.exists_baseDerivedTensor_canonical_row_completion` in
`Sheaf.Algebra.Homology.BaseDerivedTensorCanonicalRowCompletion`, without changing its
signature or existing docstring. The proof identifies the three cohomology models with
`m₁.derived` using universal derived-functor isomorphisms and constructs the boundary as the
conjugate of the derived homology shift map. Naturality and the `cohomologyIso_smul`
equations establish tensor-linearity; exactness is transported through an explicit
`ComposableArrows.isoMk₄` and reflected under restriction of scalars.

Added two proved private helpers, `restrict_exact_pair` and `restrict_exact_row`, for exactness
reflection. No definitions or public signatures changed.

## Proved and sorry left

Closed `ModuleCat.exists_baseDerivedTensor_canonical_row_completion` (node
`lem-pc-base-derived-tensor-canonical-row-completion`). No holes were added.

## No longer needed

None. The model, exactness, and published coherent-triangle imports remain needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The supplied model's scalar-action equation is sufficient to
prove tensor-linearity of the connecting map.

## New nodes

None.

## Second reading by Y3

1. Compared the delivered module with the repository version: only the proof, two private
helpers, and the proof-only import route changed; all existing declarations retain their
signatures.
2. Compiled the target module successfully with `lcompile.py`; no `sorry`, forbidden
declarations, or new public holes remain.
3. Checked the target statement and proof dependencies against the existing DAG node; the
statement is unchanged and the distinguished-triangle route is preserved.
4. Checked imports and pruning: the model, exactness, and coherent-triangle imports are all
used; no import or node can be removed.
5. Checked the proof route and edge cases described by the source docstring; the boundary is
constructed by conjugation and exactness is reflected through restriction of scalars.

Changed the import and theorem call to use the existing coherent-triangle declaration, removing
the unnecessary duplicate local module/node from this delivery.
