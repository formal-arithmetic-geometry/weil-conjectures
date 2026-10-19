## What changed

Proved the four auxiliary holes in `Sheaf.Paper.FiniteConstantModelResolution`:
`scalarAction_laws`, `scalarMap_linear`, `scalarToContinuous_isMonHom`, and
`constantScalars_commutative`. Proved the main theorem
`finite_constant_model_two_term_free_resolution` using a fully proved constant-to-continuous flatness lemma.
Every original declaration keeps its signature and visibility.

The module now contains complete private proofs of the scalar PID resolution, the field
basis sequence, preservation of exactness by the scalar encoding, finite-free transport
through all three functors, and the normalized two-term quasi-isomorphism. Both integral
and rational cases are assembled in Lean. Added
`Sheaf.Paper.ConstantToContinuousScalarFlat` and proved its flatness comparison using
`InternalSectionModuleFlat`, `FlatEquationalCriterionOfUniverses`, and Mathlib's PID
flatness and finite-relation theorems. The proof lifts finitely many scalar sections on
a common covering sieve and applies pointwise torsion-free flatness there.

## Proved and sorry left

Closed all five original holes:
- `AlgebraicGeometry.ProEtale.FiniteConstantModel.scalarAction_laws`;
- `AlgebraicGeometry.ProEtale.FiniteConstantModel.scalarMap_linear`;
- `AlgebraicGeometry.ProEtale.FiniteConstantModel.scalarToContinuous_isMonHom`;
- `AlgebraicGeometry.ProEtale.FiniteConstantModel.constantScalars_commutative`;
- `AlgebraicGeometry.ProEtale.FiniteConstantModel.finite_constant_model_two_term_free_resolution`.

Added zero holes. Also proved
`AlgebraicGeometry.ProEtale.FiniteConstantModel.constantToContinuous_preservesFiniteLimits`
(node `lem-sfb-constant-to-continuous-scalar-flat`), completing the previously retained
split in this session. Both delivered modules contain zero `sorry`s. The count is five
original holes closed and zero holes added; the new flatness theorem is proved.

Validation: both final modules compile individually without warnings through `lcompile.py`
(the flatness module in 10.5 seconds and the main module in 7.9 seconds). The final combined
`lcompile.py --all` check also passed in import order (1.6 and 1.5 seconds). The delivery
script appends its axiom probes before submission. Existing public definitions, signatures, visibility and public imports
are unchanged. There are no axioms or arbitrary witness choices in the added proof.

## No longer needed

Removed proof imports `Sheaf.Paper.CompletedConstantSheafReduction`,
`Mathlib.RingTheory.Polynomial.RationalRoot`. The current repository also imports
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`,
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`, and
`WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`; the retained sandbox omitted them.
The completion-limit and monoidal imports are unnecessary for the new proof; the DVR
statement is already available through `CoefficientExtensionFinite`.

The proof does not use `det-prop-sfb-qlbar-colimit-x-integral-limit` or
`lem-weil-pbc-completed-constant-sheaf-reduction`: direct torsion-free flatness over a PID
replaces the completion argument. It does not use the normality clause of
`lem-weil-pbc-pid-noetherian-normal`; the PID Noetherian instance remains available and
is used implicitly for the finite kernel. The scalar freeness step retains
`lem-sc-dvr-fg-torsionfree-free` through its Mathlib instance
`Module.free_of_finite_type_torsion_free'`. Definitions of constant sheaves and module
sheaf categories remain statement dependencies supplied by the unchanged public imports.
These are local dependency removals; no assertion is made that other parents stop using them.
Removed the two completion-related entries from the node's `tool_uses`; retained the DVR
entry. The unit's `realized` lists are empty and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The retained file placed `set_option` between a docstring and its declaration, which Lean
rejects; moved the option before the docstring. The retained scalar, finite-free, field,
and augmentation scratch proofs needed namespace, universe, and empty-coordinate repairs
before being integrated. The generic module-forgetful colimit instance required explicit
universe arguments to avoid unresolved `max` constraints.

The planned completion theorem is formulated using sectionwise module sheaves, whereas
this item's functor uses internal modules. Rather than leave an unstated equivalence step,
the new proof establishes direct constant-to-continuous flatness for any topological PID,
using the proved internal/section tensor equivalence and local equational criterion.
It handles the field case as well. The existing main docstring records
the old plan; the updated DAG and this report describe the implemented route.

The preceding attempt compiled both modules, but its submission was interrupted while
waiting for shared delivery capacity after an earlier preflight timeout. This retry
retained the proofs and checked them against current sources; only proof bodies,
private helpers, proof imports, and the permitted DAG proof fields differ from the
existing module. The normal delivery dry run and axiom probes validate the retained set.

## New nodes

`lem-sfb-constant-to-continuous-scalar-flat`, in
`Sheaf.Paper.ConstantToContinuousScalarFlat`, states preservation of finite limits by
extension along the canonical discrete-constant-to-continuous ring map. Its source,
full natural-language proof, and searches are recorded in the new node. Nonzero scalars
act injectively on functions pointwise, including the empty test object. All formal work
of this node is completed: finite local coefficient lifts, factorization of relations,
transport to internal flatness, and reflection through the module forgetful functor. Change record: `coord/changes/finite-constant-model-private-scope.md`. Preflight
records the two private-section variable commands as an interface change; the record
explains their scope and the unchanged public API and consumer behavior.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
