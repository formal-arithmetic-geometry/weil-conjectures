## What changed

Filled `AlgebraicGeometry.Scheme.finite_tate_transported_pullback_normalized` in
`Sheaf.Paper.FiniteTateTransportedPullbackNormalization`, retaining its statement and public
imports verbatim. Added only proved private helpers and two private proof imports:
`Sheaf.AlgebraicGeometry.AffineRootsRepresentability` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`.

The finite root projections admit a global etale presentation: pull back
`Spec Gamma(T)[t]/(t^m-1)` to T, then take the finite product representing the root tuple.
Invertibility of m proves this scheme etale. The source normalization identifies the
pro-etale pure generator with the compared etale tensor. Transposition of the canonical
pullback mate gives its image using c. The etale root pullback inclusion formula and the
level-r hypothesis identify the target roots, so the target normalization finishes.
All powers, including degree zero, use the same calculation; no root-limit/inverse-image
commutation, local tensor spanning theorem or choice of a new tower lift is required.

Updated only the item's node proof, proof dependencies and proof origin to record this
argument. No other existing module, definition, signature, instance or attribute changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finite_tate_transported_pullback_normalized`
(node `lem-amb-finite-tate-transported-pullback-normalization`).
One original hole closed; zero new holes; zero split-off statements; zero holes left in
this module. All eight private helper theorems are proved.

Validation: the complete module compiled cleanly through lcompile.py in 23.7 seconds,
with no errors or warnings. The public theorem statement and public import list were
checked verbatim against the original. The revised proof dependencies introduce no
dependency cycle back to the item. No direct-importer adaptations are required because
the public interface is unchanged.

The proof uses the existing normalized etale root pullback data; it does not claim to
remove the holes in those dependencies. This is a proof from the declared dependencies,
not a decomposition into new obligations.

## No longer needed

Removed the node's proof dependency on `lem-amb-finite-root-site-comparison` and did not
import `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison`: direct root representability
and evaluation of the kernel suffice. No existing import was removed, and no module was
withdrawn. This pruning is of this proof's dependency list, not a claim that the finite
root comparison module has no remaining consumers elsewhere.

The planned cover refinement and separatedness step are unnecessary: every finite tuple
already factors through a single etale test object. The proof also does not need
`FiniteTateLocalRootTensorsExt`, local tower surjectivity, or a generation theorem.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical error was found. The original proof plan
used a cover and the finite-root site comparison where the existing all-test-scheme
root representability theorem gives a global presentation instead.

As tools, the proof uses `lem-asd-affine-roots-representability` and
`lem-asd-etale-finite-twist-pullback` from unit `sk-prop-sf-cbc`. They provide root-scheme
representability and the existing normalized root pullback respectively; the recorded
unit route is not bypassed. No `tool_uses` approval field was edited.

Searches were actually run through msearch: LeanFinder on normalized finite Tate comparison
and pullback (eight general scalar-extension/pullback hits, no matching theorem), Loogle
on `Adjunction.homEquiv_naturality_left` (reported unknown identifier), and grep on
conjugate units, sheaf pullback and roots of unity. Local rg searches found the proved
private mate calculations in `FiniteRootSiteComparison` and the public all-test-scheme
representability theorem, which this proof reuses. The cited Stacks root-representability,
Kummer and adjoint-transformation source passages and the latest blueprint's coefficient
twist proof were read.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
