## What changed

Filled `AlgebraicGeometry.Scheme.adicPerfectQuotientSectionComparison` in
`lean/Sheaf/Paper/AdicPerfectQuotientSectionComparison.lean`, preserving its complete
statement. The private proof constructs the natural tensor/quotient comparison,
checks its successor equation as an equality of module sheaf maps on constant
quotient generators, takes terminal sections, and transports to the selected
right adjoints by adjunction uniqueness. All helper definitions have actual
constructions and all helper theorems have complete proofs.

Added `AdicPerfectQuotientSectionComparisonTensor.lean`, containing the proved public
`adicPerfectTensorQuotient_naturality` and proved private helpers for algebraic quotients, constant scalar realization, slice
restriction, tensor generators, and terminal sections. The calculation works on
an arbitrary small site; the main theorem specializes it to the coefficient site.
The proof uses Mathlib's tensor quotient equivalence and adjunction uniqueness,
and the existing complete-reduction and constant scalar comparison constructions.
The categorical transport and component-evaluation calculations use proved
private lemmas over abstract functors, so Lean need not repeatedly unfold the
completed coefficient objects. Updated the item's DAG proof and proof
dependencies to describe the implementation.
No other existing module, public interface, or target was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.adicPerfectQuotientSectionComparison`
(node `lem-sfb-adic-perfect-quotient-section-comparison`).

Original holes: 1. Holes closed: 1. Holes added: 0. Holes remaining in the
item: 0. The new helper module also has 0 holes. Its public naturality theorem is proved
by tensor induction and is used to construct the algebraic natural isomorphism. No statements were
split off.

Validation: `lcompile.py --all` compiled both modules after diagnostic options
and unused helpers were removed. `#print axioms` for the completed theorem
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. The final
compile also checked the extracted public naturality theorem and the unchanged
direct importer `Sheaf.Paper.AdicPerfectQuotientSectionAdjunction`; both compiled,
and the naturality theorem has the same three allowed axioms. The unchanged
consumer copy was removed after validation. The temporary
print command was then removed. The original theorem signature is preserved
verbatim, and every Lean line is at most 100 characters.

## No longer needed

None. No original import or declared dependency is pruned. The proof uses the
existing scalar balancing, constant scalar comparison, slice constant/sections
adjunction, and selected section model. The unit's route is preserved.

Mathlib's `TensorProduct.quotTensorEquivQuotSMul` closes the algebraic quotient
calculation; the existing sheafification and tensor APIs close the remaining
steps. No additional intermediate obligation is needed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false or changed. The existing `realizationIso` and raw
adjunction are selected from proved existence statements, so their types alone
do not provide the generator formulas needed for the successor calculation.
The proof constructs a generator-normalized realization from the same proved
constituent comparisons and then uses unique right-adjoint transport. The DAG's
three-step plan is implemented without a further split.

The argument imposes no extra assumptions on the ring, ideal, module, or site.
The tensor quotient and generator calculations cover the zero module, zero ring,
and the ideals zero and top, including exponent zero in the generic helper.

## New nodes

`lem-sfb-adic-perfect-tensor-quotient-naturality` owns
`AlgebraicGeometry.Scheme.adicPerfectTensorQuotient_naturality` in the tensor
helper module. It is fully proved and adds zero holes. This records an actual
used step, rather than splitting off an obligation. The first preflight required
a node attachment for the new helper module; extracting its existing naturality
proof supplies that attachment.

The change record is
`coord/changes/g1-adic-perfect-quotient-section-comparison.md`. Existing public
signatures and definitions are preserved; the record explains the file-local
commands detected by the static interface check.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
