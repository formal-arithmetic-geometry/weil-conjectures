## What changed

Proved `IsSepClosed.irreducibleSpace_tensorProduct` without changing its statement or
public imports. The proof follows Stacks Algebra Tag 00I7: pass to the purely
inseparable algebraic closure, reduce both factors, prove their tensor product is a
domain by the existing finite-type reduction and algebraically closed tensor-domain
theorems, and transport irreducibility back through spectrum homeomorphisms.

Four fully proved private helpers implement nil-ideal quotient homeomorphisms,
domain reductions of the base-changed factors, reduction of the right tensor factor,
and the arbitrary-domain tensor result over an algebraically closed field. The
homeomorphism helpers adapt the already proved private constructions in
`WeilConjectures.FieldTheory.SepClosedTensorReduction`, generalizing its field input
to a ring whose spectrum is irreducible. No source-library file changes.

Updated the node's proof, proof dependencies and proof origin to reflect the affine
Mathlib route and successive quotient presentation. Removed its obsolete
`lem-pc-homeo-pure-insep` tool-use approval; retained the finite-type-limit approval.
The item is not one of its unit's statement or step realizations.

## Proved and sorry left

Closed the one original hole:
`IsSepClosed.irreducibleSpace_tensorProduct`
(node `lem-zl-sepclosed-algebras-tensor-irreducible`).

Holes closed: 1. Holes added: 0. Sorries left: none. No split-off statements.
The complete Lean proof compiled cleanly through `lcompile.py` in 4.8 seconds.
The delivery command performs the final compile and axiom probes after import cleanup.

## No longer needed

Removed proof imports:

- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: already available through
  the retained field-theory imports.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`: publicly imported by the retained
  affine spectrum homeomorphism module.

- `Mathlib.AlgebraicGeometry.Pullbacks`: the affine spectrum homeomorphism is direct.
- `Mathlib.RingTheory.TensorProduct.Maps`: needed equivalences arrive through the
  retained spectrum/tensor quotient imports.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`: replaced by
  `Mathlib.RingTheory.Spectrum.Prime.Homeomorph`.
- `WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`:
  Mathlib's affine homeomorphism suffices in independent universes.

The node no longer needs `lem-pc-homeo-pure-insep` or
`lem-weil-pbc-fibre-product-affine-spectra`. No assertion is made that these are
unused by other library declarations. No modules are withdrawn. The combined
quotient-kernel computation in the old plan is replaced by two applications of
`tensorQuotientEquiv`; the nil-ideal criterion is the existing Mathlib leaf
`lem-pur-all-element-powers-spectrum-homeomorphism`.

## Where the brief, the DAG or earlier work was wrong

The mathematics of the original statement and plan is correct. Its scheme-level
base-change and affine-pullback detour is unnecessary here. The Mathlib affine
purely inseparable homeomorphism and tensor quotient equivalences implement those
steps directly. The field-case source theorem cannot itself be applied to arbitrary
rings, but its private homeomorphism argument generalizes with the given
irreducibility hypothesis. No finite generation or reducedness hypothesis is added.

Searches: LeanFinder returned purely inseparable spectrum homeomorphisms and
geometrically reduced tensor results, but no exact irreducibility theorem; Loogle
`"TensorProduct", "IrreducibleSpace"` returned zero results. Mathlib and library
text searches found the proved field-case reduction and finite-type tensor-domain
results used above. Edge cases include nilpotent elements in either factor and
arbitrary independent universes; nonemptiness is supplied by the quotient-domain
and nontrivial tensor instances. The zero ring is excluded by the original
irreducible-space hypotheses.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
