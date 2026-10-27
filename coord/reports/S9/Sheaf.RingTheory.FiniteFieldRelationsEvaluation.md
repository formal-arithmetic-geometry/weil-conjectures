## What changed

Proved `WeilConjectures.finiteFieldRelationsEvaluation` in
`Sheaf.RingTheory.FiniteFieldRelationsEvaluation`, with its signature and all definitions
unchanged. Three proved private helpers establish finite-subfield factorization,
interpolation surjectivity and the vanishing ideal of the grid. The main proof constructs
both quotient algebra equivalences and the solution/quotient-algebra-map equivalence,
then verifies every evaluation, ideal and scalar-extension clause.

The proof uses the existing unique-subfield theorem and Mathlib's finite-field roots,
indicator polynomials, combinatorial Nullstellensatz, finite-product ideal order
isomorphism and quotient first isomorphism theorem. Added the private proof import
`Mathlib.FieldTheory.Finite.Polynomial`. Updated the item's proof steps, dependencies,
origin and obsolete tool uses to match the proof.

The module compiled without errors or warnings through lcompile.py. The argument has
no nonempty-solution or positive-variable assumption: when r=0 the indicator is the
empty product 1 and the grid has one empty tuple; when S is empty restriction has
zero target and the kernel calculation still gives the unit ideal. Arbitrary model
ideals, including the zero and unit ideals, are handled through ideal maps and spans.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.finiteFieldRelationsEvaluation`
(node `lem-trf-finite-field-relations-evaluation`). Proved 1 of 1 sorries.
No holes remain in the item, no holes were added, and no statements were split off.
All three new private helpers have complete proofs.

## No longer needed

Removed redundant private proof imports `Mathlib.Algebra.Polynomial.Splits`,
`Mathlib.FieldTheory.Finite.GaloisField`, `Sheaf.FieldTheory.UniqueSubfieldOfClosure`,
and `Mathlib.FieldTheory.Finite.Basic`. The unique-subfield theorem remains needed
and is available through the unchanged public import `Sheaf.Paper.FiniteFieldFiber`;
finite-field facts used by the proof are supplied by the new Polynomial proof import.
All original public imports remain unchanged.

The separate declared proof dependencies `lem-weil-alg-closed-linear-factorization`
and `lem-weil-frobenius-polynomial-simple-roots` are unnecessary on this proof route:
Mathlib's root enumeration over the finite subfield directly supplies the product
factorization. Removed these two proof-dependency and top-level tool-use entries.
They are Mathlib leaves, so no project module is withdrawn. All other declared proof
dependencies remain used. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The planned separate factorization
in the algebraic closure and explicit Lagrange polynomials can be shortened using
existing finite-field root and indicator APIs. The planned finite coordinate-ideal
argument is already supplied by `Ideal.piOrderIso`; no finite-generation assumption
on the model ideal is needed. No definition, statement, target or consumer changed.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
