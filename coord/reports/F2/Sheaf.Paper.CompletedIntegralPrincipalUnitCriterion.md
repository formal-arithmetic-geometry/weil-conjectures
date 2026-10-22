## What changed

Implemented `WeilConjectures.completedIntegralPrincipalUnitCriterion` with its original
signature. Private proved helpers compare the categorical principal quotients with
actual scalar extension, preserve the quotient augmentations, assemble a strict tower
isomorphism, and compare both signed Roos coordinates. The final proof uses the existing
independent-universe intrinsic/Roos completeness equivalence and the Model's K-flat
computation and unit normalization.

Added proof-only imports for the existing integral completion interface, intrinsic
criterion, normalized extension-tensor comparison, tensor colimit preservation,
regular-quotient coefficient maps, single-complex tensor comparison, and Euclid's
prime-existence theorem. Updated the existing node's proof route and dependencies.
No public signature, existing definition, or target statement changed. The local
proof-context commands are documented in
`coord/changes/F2-completed-integral-principal-unit-proof-context.md`; its consumer
table records all transitive importers. No consumer is adapted.

Validation: single-file server compilation verified the complete proof. Diagnostic
messages and unused simp arguments were removed. The delivered module contains no `sorry`.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.completedIntegralPrincipalUnitCriterion`
(node `lem-weil-completed-integral-principal-unit-criterion`).

Holes closed: 1. Holes added: 0. Sorries left in the delivery: none.
No statements are split off.

## No longer needed

No original public imports were removed and no module is withdrawn. The following
planned direct dependencies are unnecessary for this proof:

- `def-sf-koszul-small-model-completed-tensor`
  (`Sheaf.CategoryTheory.RingedKoszulSmallModelCompletedTensor`): the tensor comparison
  and the completeness criterion already support independent universes on the actual site.
- `lem-pur-regular-quotient-completion-unit`
  (`Sheaf.Paper.RegularQuotientCompletionUnit`): use conditions (i) and (v) of the
  existing intrinsic/Roos criterion for the actual integral coefficient tower.
- `lem-weil-pbc-localization-universal-property`: naturality and the two normalized
  representative computations suffice; no comparison by universal derived uniqueness.
- `lem-pur-kflat-tensor-quasiiso-independent`: the quotient towers are strictly
  isomorphic, so no quasi-isomorphism argument is needed here.
- `lem-weil-proetale-countable-products-exact` and `lem-pc-kflat-resolution`: the item
  uses the existing good-complex localization and intrinsic criterion interfaces;
  these underlying theorems remain dependencies of those interfaces.

These are removals from this node's direct proof route, not claims that their modules
are unused everywhere in the project.

## Where the brief, the DAG or earlier work was wrong

The old plan and the retained theorem docstring describe transport to a small model,
a regular-quotient criterion, and universal derived-functor uniqueness. None is needed:
the published intrinsic/Roos criterion already treats the independent universes and the
actual integral reduction tower. The Model's augmentation coordinates, K-flat counit,
and unit-computes equation determine the required comparison directly.

The quotient maps are degreewise epimorphisms because tensor preserves colimits.
Consequently their normalization also determines compatibility with differentials and
transitions, without additional flatness assumptions for the strict tower comparison.
The flat-term K-flat hypothesis is used only for the existing derived completion
computations. The argument imposes no nonzero-object or nonempty-scheme condition.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
