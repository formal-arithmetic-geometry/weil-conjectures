## What changed

Closed `AlgebraicGeometry.ProEtale.integralSectionLocalModels`. The proof selects the
Noetherian qcqs branch and applies the proved cover/sieve transport and stratum assembly
helpers, reducing each member to the new one-member comparison interface. Added
`Sheaf.Paper.IntegralSectionMemberModels`, with one strictly smaller comparison theorem
left as a named sorry. Replaced the broad stratified-perfect characterization import by
the definition and coefficient transport imports used by the target. The target signature
and all existing source-library declarations are unchanged.

## Proved and sorry left

Closed one sorry: `integralSectionLocalModels`.
Added one split sorry: `integralSectionMemberModels`, which concerns one morphism and one
pro-etale member and has no cover, stratification or Noetherian hypotheses. No sorry occurs
inside a definition or private declaration.

## No longer needed

Removed `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` from the item imports; its
derived characterization and amplitude arguments are not used. The item retains the
stratified-model definition and coefficient transport modules. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The parent route requires an explicit one-member comparison interface: existing statements
do not expose transport of the scalar matrix model through the normalized section, inverse
image and slice localization. The new node isolates this smaller heart argument while the
parent proves the Noetherian branch, finite stratification and cover-to-sieve assembly. No
statement is disputed and no existing definition changed.

## New nodes

`lem-sfb-integral-section-member-models`, in
`lean/Sheaf/Paper/IntegralSectionMemberModels.lean`, states the one-member finite scalar
comparison used by the parent. Its docstring gives the matrix/cokernel and equivalence
argument and records the empty and torsion cases; its theorem is the sole split hole.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
