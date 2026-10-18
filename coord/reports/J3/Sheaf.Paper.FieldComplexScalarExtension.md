## What changed

Proved `DerivedCategory.fieldDerivedScalarExtension_preserves` in
`Sheaf.Paper.FieldComplexScalarExtension`. All existing signatures, definitions,
visibility and public imports are unchanged. Added two proof-only imports:
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` for the
already proved exact-functor cohomology comparison, and
`Mathlib.RingTheory.TensorProduct.Finite` for `Module.Finite.base_change`.
The proof retains the original finite support, maps its zero cohomology objects,
and transports finite dimensionality of base change along the comparison.
Updated the existing node's proof, proof dependencies and proof origin to describe
this proof. No definitions or statements were repaired; no consumers need adaptation.

Read the item's definition, every relevant dependency signature, the unit record
(which has no realized statement or proof steps), the original blueprint
finite-coefficient-point definition and its current main-20261015 version,
Stacks homology.tex Tag 010N and algebra.tex Tag 05G5, and the source-library
comparison construction. The argument applies to all field homomorphisms and all
cohomological degrees, including the zero object, empty support, and the identity
extension. Neither a finite extension nor finite-dimensional complex terms are assumed.

## Proved and sorry left

Closed 1 of 1 holes:
`DerivedCategory.fieldDerivedScalarExtension_preserves`
(node `def-weil-finite-dimensional-complex-scalar-extension`).
No holes added, no split-offs, and no sorry remains in the delivered module.
The final proof compiled cleanly through lcompile.py. Explicit `#print axioms`
checks for this theorem and `DerivedCategory.pointFdScalarExtension` both returned
exactly `propext`, `Classical.choice` and `Quot.sound`; diagnostic commands were
then removed from the delivered source.

## No longer needed

No existing import was removed; each supplies the predicate, scalar-extension
construction/exactness, derived functor, or additive adjunction used in this file.
No whole module is claimed globally pruned.

For this preservation obligation, the paper-specific node
`lem-weil-cohomology-commutes-scalar-extension` and its module
`Sheaf.Paper.FieldCohomologyScalarExtension` are unnecessary: the proved generic
comparison `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` supplies
exactly the needed isomorphism. Moreover that paper-specific module already imports
this item through `Sheaf.Paper.FieldDerivedScalarTower`, so importing it here would
create a cycle. Its normalized comparison, tower compatibility and quasi-isomorphism
clauses are not used. The node `lem-weil-derived-field-scalar-extension-tower`
and module `Sheaf.Paper.FieldDerivedScalarTower` are likewise unnecessary for this
preservation theorem; they remain separate parts of the overall scalar-extension
interface and are not asserted globally obsolete. The generic comparison is the
already proved declaration attached to
`lem-weil-pbc-exact-functor-bounded-below`, used as a general tool.

## Where the brief, the DAG or earlier work was wrong

The item's node had an empty proof and proof_deps despite containing a preservation
proof obligation. Its statement listed the paper-specific cohomology comparison,
but its module imports this item indirectly and cannot be imported back. The
existing generic source-library comparison avoids this cycle and closes the hole
without any new intermediate statement. The node update records that route;
statement dependencies and the unit/chapter route are unchanged.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
