## What changed

Proved `IsUniversallyCatenary.height_add_trdeg_residueField_eq` in the assigned module,
with its public statement and public imports unchanged. The proof uses one finite
polynomial presentation instead of induction on generators. Private proved helpers
establish saturated-chain height additivity under a surjection, the polynomial formula
by passage to a fibre, and compatibility of the canonical residue-field maps.
The theorem docstring and the existing node now describe this route.

The field polynomial calculation uses
`AlgebraicGeometry.minimal_component_dimension_maximum`; the relative polynomial
calculation uses `RingHom.height_eq_add_of_flat_fiber`. Both are existing declared
results, imported for proofs only. No other module or definition changes.

## Proved and sorry left

Closed 1 of 1 original holes:
`IsUniversallyCatenary.height_add_trdeg_residueField_eq`
(node `lem-exc-dimension-formula-universally-catenary-finite-type-domain`).
There are zero textual `sorry` left and zero holes added or split off. All private
helpers have complete proofs. This is a proof from the existing library declarations,
not a claim that every transitive dependency has already been discharged.

The full module was compiled with `lcompile.py`; the delivery checks also compile it
with the declaration/axiom probe. The canonical algebra structures, independent
universes, zero-generator case, zero kernel, and zero prime are covered by the proof.
Cancellation is only of the prime kernel's finite Noetherian height.

## No longer needed

Removed proof imports:
- `Mathlib.Algebra.Polynomial.FieldDivision`
- `Mathlib.RingTheory.PrincipalIdealDomain`
- `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`
- `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`
- `Mathlib.Algebra.MvPolynomial.Basic`
- `Mathlib.Algebra.Polynomial.Basic`
- `Mathlib.RingTheory.Flat.Basic`
- `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
- `Mathlib.RingTheory.Ideal.GoingDown`
- `WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`

The nine-step one-generator route is replaced by the finite-presentation proof.
The item no longer directly uses these planned dependencies:

- `lem-pur-polynomial-field-pid`: replaced by the existing general field polynomial
  dimension calculation.
- `lem-weil-pbc-simple-algebraic-extension-power-basis` and
  `def-weil-pbc-transcendence-basis`: no separate algebraic-generator case is needed.
- `def-weil-polynomial-ring`: use the finite multivariable presentation instead.
- `lem-kun-transcendence-degree-tower`: the domain tower formula suffices, including
  the generic field extensions.
- `lem-weil-pbc-localization-prime-residue-field-iso` and its module
  `WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`: use Mathlib's fibre
  correspondence and bijective residue maps directly. Its old tool-use approval is
  withdrawn from the node.
- `lem-weil-pbc-flat-height-formula`: now used through the existing flat-fibre height
  theorem, rather than imported or invoked directly. This does not prune its
  transitive use by that theorem.

The retained finite-type, domain, Noetherianity, flatness, transcendence-degree and
catenarity dependencies remain in the revised node. Some removed Mathlib imports
are available transitively from the small set of imports the proof actually uses;
no claim is made that these modules disappear from the entire targets' closure.

## Where the brief, the DAG or earlier work was wrong

The original statement is unchanged and true. Its planned one-generator quotient
argument and generator induction are unnecessary: the same saturated-chain argument
works for an arbitrary prime kernel in a finite polynomial presentation. The unit's
statement and route are preserved (its realized statement/step arrays are empty).

The two newly used upstream ring-theoretic results are generic tools from the proper
base-change unit, used only for the field polynomial calculation and the flat fibre
height identity. They do not replace any statement or step of the item's unit.
There are no new nodes, statement changes, consumer adaptations, or change records.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
