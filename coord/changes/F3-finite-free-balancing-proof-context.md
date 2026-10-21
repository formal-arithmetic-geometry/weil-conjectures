# AlgebraicGeometry.Scheme.FiniteFreeDirectImage.finiteFreeDirectImageBalancingCoherence

## Reason

Preflight requires a change record for the item module's additional commands.
The proof needs larger universe parameters, local transparency controls for the
large existing constructions, and elaboration options. It also opens the private
Conjugation namespace for proved private helpers. These commands support the
proof and do not change any public declaration's type or data.

## Old

The original statement context, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage
```

## New

The replacement context, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u uC vC rC wC
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

attribute [local irreducible] SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
  SheafOfModules.SuccessiveDerivedQuotient.pure
  proEtaleRingModules_hasDerivedCategory proEtaleRingModuleDirectImage
```

Four helper declarations additionally use the command
`attribute [local semireducible] proEtaleRingModuleDirectImage in` to expose section
maps during their proofs. Other helpers use `open ... in`, and the private
conjugation helpers are grouped in `namespace Conjugation`. All new declarations
are private and proved. All new imports are private proof imports, including two
`import all` commands accessing proved private normalization helpers.

The transparency attributes are explicitly local, the options are scoped to this
module, and namespace/open/universe commands affect elaboration of this file.
There are no new global instances or exported attribute registrations. The sole
existing public theorem retains its exact statement and is now proved; no public
definition or public import changes. Consumer statements therefore keep their
meaning.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteFreeDirectImageBalancingCoherence --uses AlgebraicGeometry.Scheme.FiniteFreeDirectImage.finiteFreeDirectImageBalancingCoherence`
reported one downstream module and the following two textual users. No claim for
the downstream module is present in the shared claim inventory.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageBalancingCoherence | F3 | One existing theorem proved, with local proof commands and private helpers. |
| Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence | unclaimed | Its two applications of the unchanged theorem remain valid; no adaptation required. |

The item compiled through the required remote single-file compiler with exit 0
in 21.2 seconds on this resumed attempt. The unchanged downstream source compiled
against the sandbox overlay with exit 0 in 4.2 seconds; no consumer source is delivered.

## Status

landed 20261021T120355-L-3854451 2026-10-21 (merge of deliver/F3/Sheaf.AlgebraicGeometry.FiniteFreeDirectImageBalancingCoherence)
