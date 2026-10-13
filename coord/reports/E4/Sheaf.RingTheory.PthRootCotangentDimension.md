## What changed

Replaced the sole sorry in `Sheaf.RingTheory.PthRootCotangentDimension`, preserving its
signature and visibility. The proof obtains a field base-change presentation, transports a
finite basis, uses geometric regularity for that field and for `ULift k`, and combines the
regular-local cotangent criterion with the proved integral-extension dimension theorem.
Residue finiteness follows from the existing finite-algebra residue-field instance.

Three new modules describe strictly lower parts of the argument:
`PthRootFieldBaseChange` proves the quotient/tensor isomorphism from the field quotient;
`PthRootFieldQuotient` proves fieldness, finiteness and the p-power assertion using the existing
root-degree theorem and the reduced-monomial dimension bound;
`PthRootMonomialDimension` proves the characteristic-free spanning/dimension bound.
All imports added to the item are proof-only. No existing statement or definition changes.

The field used by the proof is explicitly the actual quotient, then its universe lift.
Its field structure is obtained from the field-property theorem, which determines the structure.
No data are chosen from an unproved arbitrary-existence theorem.

## Proved and sorry left

Closed the item's original hole: `Algebra.pthRoot_cotangent_dimension`
(node `lem-weil-pbc-pth-root-cotangent-dimension`).

Also proved the new declarations `Algebra.pthRootAlgebra_equiv_field_baseChange`
(node `lem-weil-pbc-pth-root-field-base-change`) and
`Algebra.pthRootAlgebra_isField_finite_pow`
(node `lem-weil-pbc-pth-root-field-quotient`).

Also proved `Algebra.pthRootAlgebra_finite_finrank_le`
(node `lem-weil-pbc-pth-root-monomial-dimension`) by an explicit reduced-monomial calculation.
Each monomial image is a coefficient times a bounded monomial. The finite polynomial expansion
makes their span top, and the surjective coordinate map proves finiteness and the finrank bound.

No sorry remains in any of the four delivered modules. One original hole closed, zero added.
The target still depends on the existing library hole
`IntermediateField.pth_root_not_mem_previous_adjoin` through the root-degree theorem;
that declaration is not added or modified by this delivery.

Every delivered module compiles using lcompile.py. The reduced-monomial claim was checked
mathematically for n=0 (one constant monomial), p=1 (all variables equal coefficients),
zero coefficients (nilpotent variables), and dependent coefficients. Its proof needs only p>0.
The field claim requires independence; omitting it would be false, e.g. adjoining a p-root
of zero. The actual statement retains it. The tensor presentation allows A=0; the target's
locality excludes that case. The universe lift keeps the original independent universes u,v.

## No longer needed

No original imports were removed: all three public imports are needed by the unchanged
signature. No planned proof-dependency imports were present in the original file.
Removed the trial proof import `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` from the
item because its finite-integrality instance is already available through the required
integral-dimension module. Removed redundant imports from the new modules:
`Mathlib.FieldTheory.IsAlgClosed.Basic`, `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`,
`Mathlib.Algebra.Field.Equiv`, and `Mathlib.Algebra.CharP.Algebra`.
The reduced-monomial proof also does not need `lem-weil-pbc-monic-quotient-free`:
it uses exponent division directly in the actual quotient.

The full proof route, including the new lower nodes, no longer needs
`lem-weil-pbc-purely-inseparable-base-change-local-ring`
(`Sheaf.RingTheory.PurelyInseparableBaseChangeLocalRing`) or
`lem-weil-pbc-flat-height-formula`. Nor does it use `def-weil-pbc-flat-ring-map`.
Finite freeness is supplied directly by a tensor basis; integral injective dimension equality
replaces the zero-dimensional-fibre/flat-height argument. The residue-extension clause follows
directly from `IsLocalRing.finite_of_module_finite`.

The original root-degree, multivariate polynomial, finite-dimensional-domain-field and
pure-inseparability ingredients remain needed through the field-quotient/base-change nodes.
The geometric regularity, regular-ring and regular-local cotangent nodes remain directly needed.

## Where the brief, the DAG or earlier work was wrong

The plan was mathematically sound but longer than necessary. The already proved declaration
`ringKrullDim_eq_of_isIntegral` in
`WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp` eliminates the flat height/fibre calculation.
The existing docstring still describes the former route; its API text is preserved, while the
DAG proof and this report describe the actual route. No false statement or forced adaptation.

## New nodes

`lem-weil-pbc-pth-root-monomial-dimension` is the proved dimension bound, obtained by
reducing each exponent modulo p. Its source is the quotient presentation in Stacks 07E5
and monic division. It is substantially simpler than the item: there is no geometric
regularity, local ring, residue field, differential independence or characteristic hypothesis.

`lem-weil-pbc-pth-root-field-quotient` records the proved comparison with the root-generated
field of degree p^n from 07DZ. Evaluation is surjective; the monomial dimension bound makes
it injective. Polynomial induction proves the p-power assertion.

`lem-weil-pbc-pth-root-field-base-change` records the proved tensor identification in 07E5.
The proof computes the mapped generators, uses the polynomial tensor and quotient tensor
isomorphisms, and lifts the explicitly constructed field quotient to universe max u v.

Searches: LeanSearch returned Internal Server Error (unavailable, no mathematical verdict).
LeanFinder returned one-variable AdjoinRoot field/power-basis facts and unrelated Krull-dimension
bounds, with no whole-statement match. Grep in Mathlib, WeilConjectures, Sheaf and the DAG found
the polynomial tensor equivalence, quotient tensor equivalence, and existing root-degree theorem,
which the proofs use. Blueprint searches for p-th roots and monic found no duplicate statement.
Sources read online: https://stacks.math.columbia.edu/tag/07E5,
https://stacks.math.columbia.edu/tag/07DZ and https://stacks.math.columbia.edu/tag/00OK.
The unit and chapter route are preserved; the item's node realizes no unit-level step itself.


## Second reading by E4

1. Compared the item with the repository using diff. Its existing signature,
   visibility, definitions and three public imports are byte for byte unchanged;
   only proof imports and the proof were added. The other three modules and nodes
   are new, strictly lower results. No statement change or forced adaptation.
2. Compiled all four modules in import order with lcompile.py: no errors or
   warnings. Scanned for sorry and prohibited declarations: none in the delivered
   sources. A scratch import probe printed axioms for every delivered theorem.
   The monomial bound has only propext, Classical.choice and Quot.sound. The other
   three additionally have sorryAx from the existing root nonmembership dependency,
   as already disclosed above. Q is the explicit quotient and F its lift; IsField.toField
   supplies the unique field structure on that ring, not an arbitrary existence witness.
3. No new hole is split off. Read each new statement and proof, checking n=0,
   p=1 for the characteristic-free bound, zero/dependent coefficients, and A=0
   for the presentation. Independence correctly excludes nonfield quotients such
   as k[X]/(X^p). Repeated searches with Loogle `MvPolynomial, Module.Finite`,
   LeanFinder on bounded-exponent spanning for multivariate monic quotients, and
   rg on quotient finrank, monomial spans, field adjunction and tensor quotients.
   Results gave restricted-degree subspaces and one-variable power bases, not a
   direct shorter replacement. Existing tensor and adjunction lemmas are used.
4. Read the argument from the item downward. The finite free faithful extension
   justifies integral dimension equality and finite residues; geometric regularity
   applies to the explicitly lifted fields in the correct universes. The original
   public imports are signature dependencies; new proof imports supply the tensor,
   dimension and lift operations used. The report accounts for all old proof_deps:
   retained ingredients through the new nodes and the three bypassed nodes.
   Checked dag/units/sk-thm-p1.json: the item and bypassed nodes realize none of
   its statement or steps. The unit and chapter route are preserved.
5. Read all four node records and compared their proof steps and proof_deps with
   the Lean. The listed dependencies match the quotient, tensor, regularity and
   integral-dimension argument; each new node has the required source, searches,
   origin, creation, blueprint, chapter, unit and Lean fields. Repaired the three
   new lean.statement fields to contain the exact multiline declaration signatures.

Changes in this reading: repaired those verbatim signature records and rewrote
only the new field-base-change theorem's proof docstring to describe its actual
quotient-and-lift construction. No Lean proof, hypothesis, conclusion or import
was changed. One original hole closed; zero new holes added; no decomposition
into open statements. Global pruning remains the maintainer's closure calculation.
