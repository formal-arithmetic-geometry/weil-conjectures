## What changed

Proved `WeilConjectures.constantExtensionResidueCompositum` without changing its
statement or any definition. The proof retains the actual two residue embeddings:
the tensor map is surjective, its kernel quotient is the residue field, and its
two factor images generate that field. Arithmetic Frobenius gives the lcm degree;
the tower law and finite-vector-space cardinality give the remaining formulas.

Added the proved general finite-field base-change lemma
`AlgebraicGeometry.finiteFieldBaseChangeResidue_surjective` in
`Sheaf.AlgebraicGeometry.FiniteFieldBaseChangeResidueSurjective`. Its proof uses
the finite image subring, the scheme pullback universal property and the
field-valued-point correspondence. All auxiliary finite-field and pushout
calculations in the item module are private and proved. The item's DAG proof now
records this direct finite-field route. Public imports and existing signatures
are unchanged.

## Proved and sorry left

Closed: `WeilConjectures.constantExtensionResidueCompositum`
(node `lem-zl-constant-extension-pullback-return-residue`).

Left unchanged: `WeilConjectures.constantExtensionPullbackReturn`
(the same node). This is the one remaining `sorry` in the item module.

Added holes: none. The new public theorem
`AlgebraicGeometry.finiteFieldBaseChangeResidue_surjective`
(node `lem-zl-finite-field-base-change-residue-surjective`) is proved.
The coordinate-successor and residue-compatibility proofs from J2's earlier
landing are retained and are not counted as new holes closed by this delivery.

## No longer needed

The residue proof does not use
`lem-weil-pbc-fibre-product-point-residue-field` or
`WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`: the finite
image is already a field and the pullback universal property identifies it with
the residue field directly. Removed that node from the item's `proof_deps`, proof
steps and `tool_uses`, retaining the remaining approvals in order. This does not
withdraw the upstream declaration or its module; other consumers may still need
it. No source-library declaration is changed or removed.

Removed the exploratory private imports
`Sheaf.CategoryTheory.CyclicReturnExactEquivalence` and
`WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`. The former is
still a dependency of the unproved normalization plan; no claim that it can be
pruned from the project is made. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The initially available shared source still had four holes, although the current
node's J2 review recorded that the coordinate-successor and residue-compatibility
holes had been closed. The shared source synchronized during this session;
this delivery preserves the synchronized proofs and counts progress against its
two-hole baseline.

The planned generic fibre-product residue theorem is stronger than needed here.
For a closed point over a finite field, its residue field is a finite set; the
image-field proof avoids fraction fields altogether. The assertions and unit
route are unchanged. Edge cases checked: empty schemes are vacuous; m=1 gives
relative degree one; common factors of d and m are retained by the gcd/lcm
formula, and no tensor product is assumed to be a field or split.

## New nodes

`lem-zl-finite-field-base-change-residue-surjective` is the proved finite-field
special case of the residue-field clause in Stacks Tag 01JT. Its new module
contains one public theorem and no holes. The node records its source, the
complete three-step proof, three Mathlib searches and the verbatim Lean
statement. It uses the already approved closed-point field criterion and
Mathlib's residue-field-point naturality and field-point correspondence. No
change record is needed: no existing statement or definition changed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
