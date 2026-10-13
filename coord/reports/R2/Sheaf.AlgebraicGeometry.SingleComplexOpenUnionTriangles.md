## What changed

Replaced the hole in `AlgebraicGeometry.singleComplexOpenComparison_union_triangles`
by a compiling proof from a chain-level short exact comparison presentation.
The proof defines all six triangle arrows, proves distinguishedness by explicit
triangle isomorphisms, and conjugates Mathlib's short exact triangle morphism.
The three component equations follow by iso cancellation. No existing signature,
definition, or public import changed. Added a proof-only import of
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESPresentation` and updated the
parent node's proof route.

Read Stacks [08HZ](https://stacks.math.columbia.edu/tag/08HZ),
[08HY](https://stacks.math.columbia.edu/tag/08HY), and
[0DJ9](https://stacks.math.columbia.edu/tag/0DJ9) online because the source TeX
files are not present in this clone. Also read
[013N](https://stacks.math.columbia.edu/tag/013N) and
[013O](https://stacks.math.columbia.edu/tag/013O) for the cylinder factorization
and its homotopy equivalence. These supply the relative restriction
sequence, counit comparison and induction diagram. The unit record has no
realized statement or step that this reduction bypasses.

## Proved and sorry left

Closed the original named hole:
`AlgebraicGeometry.singleComplexOpenComparison_union_triangles`
(node `lem-pc-single-complex-open-union-triangles`). Its proof has no sorry.

Added one named hole:
`AlgebraicGeometry.singleComplexOpenComparison_union_ses_presentation`
(node `lem-pc-single-complex-open-union-ses-presentation`). This new theorem
constructs a diagram of short exact cochain complexes and identifies its
localized components; it asserts no boundary or distinguished triangle.
The final triangle construction and all three component verifications are
proved in the original module. This is a decomposition, with one hole closed,
one added, and net zero; the geometric presentation remains unproved.
There are no other sorries in the delivered files.

## No longer needed

No imports removed and no modules globally pruned. The parent's old direct
proof dependencies now belong to the new presentation node (the short exact
triangle node remains a direct dependency of the parent). They are still needed
for the geometric presentation and are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The existing relative-MV implementations cannot be imported here:
`import_direction.py may` rejects RelativeMVCanonicalTriangles,
RelativeMVPinnedTriangleComparison, RelativeMVPinnedVertexComparisons and
DerivedBaseChangeMayerVietorisBoundary, since each already reaches this item.
The existing RelativeMVSESPresentation also requires a cover of all X, whereas
this statement permits any compact union. DerivedOpenUnionSESPresentation is
for a single coefficient and does not identify base-change components.
No mathematical statement was changed or disputed.

LeanFinder and Loogle found Mathlib's short exact triangle construction and
naturality. The grep search found the single-coefficient open-union presentation
and the cyclic global-cover implementation, but no usable geometric diagram.
LeanSearch returned Internal Server Error and is recorded as unavailable.
The new presentation was checked on empty, repeated and contained opens, zero
coefficients, and arbitrary coefficient maps in its docstring; these yield
zero or split restriction rows without invertibility hypotheses.

## New nodes

`lem-pc-single-complex-open-union-ses-presentation` is the chain-level part of
the existing Stacks 08HZ/08HY construction on the union. It records the strict
comparison diagram, a functorial cylinder replacement, and the three conjugacy
identifications. The new module contains its one named sorry, with source and
proof in words. The existing parent node records the proved Mathlib triangle
construction from this presentation. No change record or forced adaptation is
needed.

## Second reading by R2

1. **Statements and interfaces.** Compared the delivered triangle module with
the repository version at every existing declaration. The signature of
`singleComplexOpenComparison_union_triangles` is unchanged; the only interface
addition is the proof-only import of the chain-level presentation. Verdict:
pass.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py`.
The triangle theorem contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`,
or `implemented_by`; its only unresolved dependency is the named presentation
theorem, whose `sorry` is explicit and documented. The proof uses
`triangleOfSES`, `Triangle.isoMk`, distinguishedness transport, and the three
presentation equations exactly as stated. Verdict: pass.

3. **Split-off statement.** Read the chain-level presentation node and its Lean
declaration. It is strictly below the target: it supplies only short exact
complexes, a morphism, and localized component equations, with no connecting
morphisms or distinguished triangles. Its source, proof sketch, edge cases,
and node metadata agree. Verdict: pass; one documented hole remains by
decomposition.

4. **Pruning and imports.** The new presentation theorem is the sole new proof
dependency. The parent keeps all public imports required by its signature,
while the presentation is imported privately for proof use. No unused import
or old proof dependency was removed, and no target or unit statement was
bypassed. Verdict: pass.

5. **DAG agreement.** The parent node records the presentation and SES-triangle
routes used by the proof; the new node records the chain-level route and its
Lean declaration. The unit's `realized` data is unchanged and no statement or
definition was altered. Verdict: pass.

Changed only the parent proof, added the proof-only presentation import, and
added this review record; no mathematical statement or definition changed.
