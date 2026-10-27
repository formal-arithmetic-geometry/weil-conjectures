## What changed

Proved `smooth_dimension_clopen_partition`: the local fibre dimension is locally
constant, has finite image on the quasi-compact source, and its natural-number
level sets are disjoint clopen subschemes covering the source. Local smooth charts
prove the relative-dimension claim, including empty loci; closed immersions and
composition give finite type and separatedness.

Proved the finite gluing and bound-detection argument in
`varyingDimension_finite_dualizing_inverse`, reducing its pure-dimensional inverse
input to `Sheaf.Paper.SmoothFiniteDualizingInverse`. A proved private categorical
helper lifts both specified inverse maps through the actual product restriction
equivalence and proves their component equations. It works also for the empty
family. The finite exceptional comparisons are evaluated on the existing
`clopenFiniteUnitAt`, and all functors, units and tensors are unchanged.

The new import is private to the proof. Existing public signatures, definitions,
instances, attributes and public imports are unchanged. No other existing Lean
module is changed. The finite gluing proof does not use injectivity of the labels
or nonemptiness of the components; both original binders are retained, with only
a local unused-section-variable linter setting on that theorem.

Both delivered Lean modules compiled successfully with `lcompile.py --all`.
The original theorem signatures and assembly definition were also checked against
the repository copies.

## Proved and sorry left

Closed the original holes in
`WeilConjectures.PurityFiniteSetting.smooth_dimension_clopen_partition` and
`WeilConjectures.PurityFiniteSetting.varyingDimension_finite_dualizing_inverse`.
The former is proved; the latter is a decomposition with its gluing and interval
clauses completely proved.

Added one hole:
`WeilConjectures.PurityFiniteSetting.smooth_finite_dualizing_inverse`
(node `lem-pur-smooth-finite-dualizing-inverse`). This is the pure-relative-dimension
finite-coefficient inverse calculation only; it asserts neither a partition,
restriction comparisons, prescribed component maps, nor interval detection.

Left the original hole in
`WeilConjectures.PurityFiniteSetting.varyingDimension_dualizing_inverse`
(node `lem-pur-varying-dimension-dualizing-inverse`): the coherent integral and field
assembly remains unchanged. Total: two original holes closed, one new hole added,
one original hole left; two textual holes remain in the packet.

## No longer needed

Removed the item's direct proof import
`Sheaf.AlgebraicGeometry.SmoothTensorDuality`: the finite use belongs to the new
pure-dimensional inverse step. Its declaration remains a dependency of that step,
and the unchanged integral proof plan still needs the smooth-line argument.

No dependency node or existing module is withdrawn. The integral/field assembly
still needs the existing complete-residue-line and coefficient-transport nodes.
The original unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or changed. The geometric argument needs no absolute
separatedness of either scheme. Its finite-image argument must use the actual
structure morphism of the Over object to obtain compactness. The finite argument
uses the ambient restriction equivalence as well as finite-Tor detection, so
prescribed inverse maps can be lifted without requiring a new tensor-closure
lemma for the constructible subcategory.

## New nodes

`lem-pur-smooth-finite-dualizing-inverse`, in
`lean/Sheaf/Paper/SmoothFiniteDualizingInverse.lean`, isolates the pure-dimensional
finite-coefficient part of Step 4 of the original node. Its docstring and node give
the shifted-line proof and the required comparison to the actual intrinsic
exceptional functor and tensor. Its statement includes empty sources and dimension
zero. No change record is needed: existing statements and data are untouched.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
