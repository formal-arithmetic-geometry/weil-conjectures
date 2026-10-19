## What changed

Retained the earlier attempt's proofs of quotient compatibility, the kernel ideal,
scalar-extension laws and additivity, the ordinary strict-limit unit, the compatibility
of Koszul completion with restriction, and the tower restriction/additivity lemmas.
Removed the temporary `#exit` and profiler option. Added direct specializations of the
existing cochain derived-change-of-rings model and strict-tower derived-limit theorem.
The existing cochain-model dependency supplies the derived-extension universal pair.
Added `Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory` for tower exactness.
Also proved inverse-image projection naturality from the limit cone equations and
constant-sheaf comparison naturality, extending adjacent transitions by
`NatTrans.ofOpSequence`. Proved ordinary inverse-limit restriction using the existing
`siteRestrictScalars_preservesLimits`, Mathlib's natural limit comparison, and joint
monicity of the limit projections to prove uniqueness of the complex isomorphism.
Statements, definitions, universes and visibility are unchanged.

## Proved and sorry left

Closed 15 of 39 original holes; no holes added and no new splits.
The following names are relative to `CategoryTheory.ConstantCompletion`.

Closed:

- `quotient_step`
- `kernelIdeal_existsUnique`
- `change_laws`
- `change_additive`
- `derivedExtension_exists`
- `reductionTower_additive`
- `strictLimit_exists`
- `ordinaryUnit_existsUnique`
- `koszul_quotient_restriction`
- `tres_exact`
- `restrictionReduction_additive`
- `reductionRestriction_additive`
- `reductionRestriction_preservesZero`
- `pulledProjection_naturality`
- `limitRestriction_existsUnique`

Remaining, all attached to node `lem-weil-pbc-constant-completion-equivalence`:

- `flat_and_quotients`
- `equivalence`
- `finiteComparison_existsUnique`
- `finiteDerivedComparison`
- `reductionStep_existsUnique`
- `reductionUnit_existsUnique`
- `quotientPresentation_exists`
- `koszul_quotient_reflector`
- `completion_restriction`
- `reductionTowerComparison_existsUnique`
- `derivedReductionTowerComparison`
- `derivedLimitRestriction`
- `insertion_existsUnique`
- `inverseImageData_exists`
- `pull_additive`
- `derivedPull_exists`
- `ordinaryPullComparison_existsUnique`
- `derivedPullComparison_existsUnique`
- `ordinaryFinitePull_existsUnique`
- `finitePull_existsUnique`
- `completedFinitePull_existsUnique`
- `pullbackTowerComparison_existsUnique`
- `pullback_composition`
- `pullback_identity`

## No longer needed

No imports, dependency nodes or transitive modules are pruned. All current dependency
imports are retained, including dependencies added to the shared source during this session.
The remaining proof imports still belong to uncompleted clauses of the node's plan.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the brief or DAG was found. The retained proofs were checked
against the current shared source: 39 holes before, 24 after, with all 15 closures
listed above and no additional holes. A fresh remote compile through `lcompile.py`
passed cleanly in 33.5 seconds on 2026-10-19. No source lines exceed 100 characters,
and the diff changes no existing signatures or definitions.
The cochain-model interface already supplied by the declared derived-change-of-rings
node is shorter than transporting the homotopy counit manually.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
