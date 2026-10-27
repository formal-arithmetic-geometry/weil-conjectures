## What changed

Replaced the single hole in
`CategoryTheory.finiteKoszulTensor_acyclic_of_residue` by a proof with its original
signature. Choose a termwise-flat K-flat replacement, compute its residue
extension using the existing universal comparison, kill each homology sheaf of
the finite dual Koszul stage, apply its finite Postnikov tower, and transfer back
through the tensor-cone comparison.

Added three proved modules:

- `Sheaf.Algebra.Homology.DualKoszulHomologyTorsion`: constructs the negative
  two-term contractions, tensors them across the ordered factors, applies the
  finite-generator pigeonhole bound, and transports to the actual internal dual.
  It also proves the dual's support is contained in `[-r,0]`.
- `Sheaf.Algebra.Homology.NilpotentCoefficientTensorAcyclic`: constructs the
  quotient action on kernel-annihilated module sheaves, proves the cancellation
  comparison for their tensor complexes, and inducts on the ideal-power exponent.
  Global scalar endomorphisms allow the existing categorical image-cokernel
  filtration to be used without constructing a new ideal sheafification theory.
- `Sheaf.Algebra.Homology.BoundedHomologyTensorAcyclic`: applies the published
  exact K-flat tensor functor to a finite ordered Postnikov tower, with all shift
  and representative comparisons made explicitly.

Attached the already proved source-library theorem
`CategoryTheory.exists_shortExact_of_smul_eq_zero_of_mem_pow_succ` to a new
source-backed node. The source module is imported without modification.
All added imports in the item are proof imports. No existing public interface,
definition, instance, attribute, target statement, or adopted source file changes.

## Proved and sorry left

Closed the item's one original hole:
`CategoryTheory.finiteKoszulTensor_acyclic_of_residue`
(`lem-sfb-finite-koszul-residue-acyclic`).

Also proved, with no holes:

- `CategoryTheory.dualKoszul_bounded_torsion`
  (`lem-sfb-dual-koszul-homology-torsion`);
- `CategoryTheory.tensor_acyclic_of_nilpotent_coefficient`
  (`lem-sfb-nilpotent-coefficient-tensor-acyclic`);
- `CategoryTheory.tensor_acyclic_of_bounded_homology`
  (`lem-sfb-bounded-homology-tensor-acyclic`).

Holes closed: 1 of 1. Holes added: 0. Sorries remaining in the delivered Lean
files: 0. Split-off unfinished obligations: 0. The source-backed scalar-filtration
node points to an existing proved declaration, not a new obligation.

Remote compilation passed without warnings for all four delivered modules. The
final item compile took 7.7 seconds; the coefficient proof took 15.9 seconds;
the bounded and dual Koszul helpers took 4.8 and 1.5 seconds in the successful
helper batch. Every delivered node has consistent dependency lists, no cycle
through it, and a Lean statement matching its declaration.

Edge cases checked in the statements and proofs: empty generator lists, exponent
zero, zero modules and zero rings; the bounded criterion also allows reversed
bounds, in which case the input is zero. There are no nonzero, Noetherian,
regular-sequence, completeness or boundedness hypotheses on the original complex.

## No longer needed

No import from the original item was removed: it originally imported only
`Sheaf.Paper.ConstantCompletionEquivalence`. No Lean module is withdrawn.

The old direct dependency `lem-pur-derived-change-of-rings`, implemented in
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, is unnecessary for this
proof: its theorem concerns ordinary module categories, while
`ConstantCompletion.derivedExtension.computation` already computes the actual
ringed-site extension occurring in the statement.

The other old dependencies remain necessary through the proved helper modules:

- `lem-pur-kflat-change-of-rings-all-independent`,
  `lem-pur-change-of-rings-tensor-cancellation-independent`, and
  `lem-pur-acyclic-kflat-tensor-arbitrary` are used by the nilpotent coefficient proof.
- `lem-weil-pbc-ordered-koszul-homology-torsion` supplies the scalar-natural-
  transformation and finite-generator annihilator calculus reused by the new
  negative-model proof. Its positive-model conclusion alone is not substituted
  for a statement about the actual dual.
- `lem-sfb-bounded-postnikov-extension-generation` is used by the bounded criterion.
- `lem-pc-bounded-above-flat-kflat-site` remains underneath the existing theorem
  `lem-weil-pbc-ringed-cech-koszul-dual-kflat`, which is used directly for transfer
  from the replacement to the original complex.

The new main-node proof dependencies record these proved intermediate interfaces;
no unused extra Koszul, completion, or inverse-limit lemma is imported.

## Where the brief, the DAG or earlier work was wrong

The earlier plan's ordinary-module derived-change-of-rings theorem does not have
ringed-site sheaf coefficients. The already present computation field of
`ConstantCompletion.derivedExtension` supplies the needed comparison with the
precise functor used by the hypothesis.

The finite scalar filtration was already proved in
`WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeResidueIdeal`, but had
no DAG attachment. The existing global-sections linear structure on module
sheaves makes it applicable here. This closes the nilpotent-coefficient step
without another split of the same residue-vanishing obligation.

The original node statement is retained. The unit's realized nodes and proof
route are retained. There is no statement or definition repair and no change record.

## New nodes

`lem-sfb-dual-koszul-homology-torsion` records the proved support and torsion
statement for the actual finite internal dual. Its new module has no holes.

`lem-sfb-bounded-homology-tensor-acyclic` records the proved finite Postnikov
tensor-vanishing criterion. Its new module has no holes.

`lem-sfb-nilpotent-coefficient-tensor-acyclic` records the proved coefficient-module
vanishing theorem. Its new module has no holes.

`lem-sfb-finite-scalar-ideal-filtration` attaches the existing, proved abstract
image-cokernel scalar-filtration theorem. It adds no Lean module or declaration.

All four serve the finite-stage Tag 0G1T calculation in the Tag 0G1U
residue-zero-detection argument, below `det-lem-integral-models-stacks`.
The current blueprint was searched for Koszul homology, bounded Postnikov,
nilpotent tensor, filtration ideal and scalar ideal; none of the matches states
one of these four precise claims. Mathlib searches are recorded from the actual
search log, using LeanSearch, LeanFinder, Loogle and grep for each node.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
