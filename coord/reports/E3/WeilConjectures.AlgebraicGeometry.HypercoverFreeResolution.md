## What changed

The four canonical hypercover free-resolution theorems are now proved by real Lean
assembly from eight strictly smaller degree-component theorems. The free abelian and
free module quasi-isomorphisms use `quasiIso_iff`, splitting degree zero from positive
degrees. The two injective section conclusions combine their degree-zero exactness
components with positive-degree vanishing components. The eight component theorems
are new statement nodes and remain `sorry` for a later proof. The item's node records
these proof dependencies.

## Proved and sorry left

Closed in the item:

- `AlgebraicGeometry.SplitEtaleHypercover.freeAbelian_augmentation_quasiIso`.
- `AlgebraicGeometry.SplitEtaleHypercover.injective_abelian_section_cohomology`.
- `AlgebraicGeometry.SplitEtaleHypercover.freeModule_augmentation_quasiIso`.
- `AlgebraicGeometry.SplitEtaleHypercover.injective_module_section_cohomology`.

Added component sorries, each with its own node:

- `hypercover_freeAbelian_quasiIsoAt_zero` and `hypercover_freeAbelian_quasiIsoAt_pos`.
- `hypercover_freeModule_quasiIsoAt_zero` and `hypercover_freeModule_quasiIsoAt_pos`.
- `hypercover_injective_abelian_zero` and `hypercover_injective_abelian_positive`.
- `hypercover_injective_module_zero` and `hypercover_injective_module_positive`.

## No longer needed

No imports or existing proof-dependency nodes were pruned. The component modules are
proof-only imports of the item and are required by its assembly proofs.

## Where the brief, the DAG or earlier work was wrong

The original four canonical declarations had no compiled proof route available in the
library. The stated Stacks route requires the missing generic hypercover induction and
matching-object arguments. This delivery records the degree-zero and positive-degree
parts explicitly so that those arguments can be proved independently without moving a
whole target statement under a new name.

## New nodes

Eight component nodes were added under `dag/nodes/sec-curve-estimates/`, each with one corresponding module under `lean/Sheaf/AlgebraicGeometry/`:

- `lem-weil-pbc-hypercover-free-abelian-positive`.
- `lem-weil-pbc-hypercover-free-abelian-zero`.
- `lem-weil-pbc-hypercover-free-module-positive`.
- `lem-weil-pbc-hypercover-free-module-zero`.
- `lem-weil-pbc-hypercover-injective-abelian-positive`.
- `lem-weil-pbc-hypercover-injective-abelian-zero`.
- `lem-weil-pbc-hypercover-injective-module-positive`.
- `lem-weil-pbc-hypercover-injective-module-zero`.

## Earlier second reading (a previous round; superseded)

The assembly proofs compile and use each component as a strict degree or conjunction part. The new component statements preserve the original objects and hypotheses; their proofs remain open for a subsequent worker.

## Second reading by E3

1. I compared the delivered source module with the repository version. Every existing
   declaration has the same signature; only proof bodies and proof-only imports changed.
   Verdict: pass.
2. I compiled the item and all eight added modules with `lcompile.py`. The four parent
   declarations have no `sorry`; the eight explicitly named component declarations are
   the only remaining holes. No forbidden declaration or definition hole is present.
   Verdict: pass.
3. I checked each split statement against the parent statement and the Stacks route. Each
   is a proper degree or coefficient component, with a source docstring and a matching
   node; none merely renames the parent theorem. Verdict: pass.
4. I checked the route and pruning. The parent still assembles the degree-zero and
   positive components with `quasiIso_iff`, and the injective conclusions still combine
   their two components. No existing import can be removed without changing the route.
   Verdict: pass.
5. I checked the node records against the Lean declarations and corrected component
   proof dependencies so they flow through the lower Cech, coskeleton, Yoneda, and
   injectivity arguments without depending circularly on the parent node. Verdict: pass.

I changed the report, repaired the eight component node dependency records and proof
descriptions, and left the compiled Lean proofs unchanged.
