## What changed

Proved `RingHom.isReduced_of_isRegular` in
`Sheaf.RingTheory.RegularMapReducedTarget` without changing its signature.
The proof follows all five steps of the node: regular fibres are reduced by
regular-local domains and joint injectivity of prime localizations; Serre's
criterion and flat ascent of `(R_0)` and `(S_1)` then give reducedness of the target.
The degree-one residue-field extension is represented by `ULift` to meet the
universe bound in geometric regularity. Its tensor product is identified with
the original fibre by `TensorProduct.congr` and `TensorProduct.lid`.
Added the proof import `Mathlib.Algebra.Field.ULift` and clarified this universe
step in the docstring and node. No definitions, statements, or consumers changed.

## Proved and sorry left

Closed the module's one hole: `RingHom.isReduced_of_isRegular`
(node `lem-exc-regular-map-reduced-target`).
Holes added: zero. Holes left in the delivered module: zero.
No split-offs or new declarations.

Validation: on resumption, `lcompile.py` compiled the module cleanly in 7.4 seconds.
The required `deliver3.py --no-push` dry run passed compilation and preflight.
`#print axioms RingHom.isReduced_of_isRegular` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed `import Sheaf.AlgebraicGeometry.IsRegularScheme`: the proof uses only
the ring clauses of `def-weil-regular-scheme`, supplied by Mathlib through the
existing public `Sheaf.RingTheory.GRing` import. The scheme clause and its
module are not needed for this item. Kept `def-weil-regular-scheme` as a proof
dependency because its ring clauses are used.
Removed the redundant direct proof import `Mathlib.RingTheory.RegularLocalRing.Defs`;
its declarations are already public dependencies of `Sheaf.RingTheory.GRing`.
All seven declared proof dependencies remain used. No DAG node is pruned, and
no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is correct, including empty prime spectra and zero fibres.
The literal identity field may have the wrong universe for the quantified finite
extension in `Algebra.IsGeometricallyRegular`; a canonically isomorphic `ULift`
fixes this without any statement or definition change.
Searches with leanfinder, loogle (`IsReduced, Module.Flat`) and grep found no
shorter ring-theoretic ascent result. The existing private `regular_of_geometric`
proof in `Sheaf.RingTheory.PopescuPolynomialKernelParameters` supplied the
universe-lift pattern; that large, unrelated module is not imported.
The unit record `sk-prop-a1-kummer` has no realization attached to this node;
the proof preserves the assigned algebra route.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
