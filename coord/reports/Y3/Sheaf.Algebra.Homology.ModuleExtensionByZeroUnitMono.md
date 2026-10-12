## What changed

Proved `AlgebraicGeometry.moduleExtensionByZero_unit_mono` with the existing chosen
adjunction and Mathlib `Adjunction.unit_mono_of_L_faithful`. Its signature is unchanged.
Added `ModuleExtensionByZeroUnitFaithful.lean` and proved
`AlgebraicGeometry.extensionByZero_faithful`: the direct-sum extension presheaf is
separated, so its locally injective sheafification unit is injective. Naturality
reflects equality to the extension presheaves, and their summands recover the
original morphisms. Both added imports in the item's module are proof-only.
The helper publicly imports only modules needed for its signature and privately
imports Mathlib's local-injectivity tools. No statement or definition changes.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.moduleExtensionByZero_unit_mono`
(node `lem-sc-module-extension-by-zero-unit-mono`). Also closed the first worker's
proposed hole in `AlgebraicGeometry.extensionByZero_faithful`
(node `lem-sc-module-extension-by-zero-unit-mono-faithful-aux`). No sorry remains
in either delivered module; no hole is added relative to the repository. This
closes one existing hole and adds a proved helper, rather than a decomposition.
Both declarations have only `propext`, `Classical.choice` and `Quot.sound`
in their axiom closures. Neither proof chooses arbitrary data from a mere existence theorem:
the chosen adjunction is the unchanged existing choice, and the proof works for
any adjunction on these functors.

## No longer needed

No repository import is removed, and no module is claimed pruned. The old direct
proof dependencies `def-weil-extension-by-zero-presheaf` and
`def-weil-presheaf-modules-sheafification` are used by the proved faithfulness
helper instead of directly by the unit-monicity argument; both remain required
in the closure. `lem-sc-derived-open-restriction-adjunction-exact` remains a
direct proof dependency of the item. The helper no longer imports
`OpenRestrictionAdjunctionExact` or Mathlib `Adjunction.FullyFaithful`.

## Where the brief, the DAG or earlier work was wrong

The first worker's report described direct stalk-map dependencies absent from
this item's old proof_deps, and omitted the chosen adjunction from the updated
proof_deps. Both are corrected. The first helper docstring's assertion about
sheafification preserving distinctions lacked the necessary separation argument;
the completed proof supplies it. The originally supplied search records were
not backed by this sandbox's search log; actual independent leanfinder, loogle,
and grep searches now support the new node. LeanSearch was also attempted and
recorded as unavailable (Internal Server Error); no mathematical verdict is
inferred from that failure. No interface change record is
necessary for private proof imports; the unnecessary record is removed.

## New nodes

`lem-sc-module-extension-by-zero-unit-mono-faithful-aux` is the proved faithfulness
helper in `ModuleExtensionByZeroUnitFaithful.lean`. Its node records separation,
local injectivity of the sheafification unit, and recovery on direct-sum summands,
with the construction and sheafification dependencies. No change records.

## Second reading by Y3

1. Compared the delivered item to the repository with diff: the existing theorem
   signature, visibility, and definitions are byte-for-byte unchanged. Pass.
2. Compiled both modules with lcompile.py in import order without warnings. There
   are no sorry, axiom, unsafe, opaque, implemented_by, or extern declarations.
   A scratch copy with #print axioms shows only propext, Classical.choice and
   Quot.sound for both the new faithful theorem and the unit theorem. Pass.
3. No split-off statement remains open. Independently searched Mathlib with
   leanfinder, loogle and grep using separation and local-injectivity terminology,
   and searched lean/ for related extension functor results. LeanSearch was
   attempted and returned Internal Server Error, recorded as unavailable. The related scheme
   stalk results depend on this unit theorem and would form a cycle. The helper
   now has a complete proof. Checked empty W, W = X, and zero modules: empty
   direct sums give vacuous separation, while each object over W has its unique
   injection, including the empty open. Checked the stated source claims at
   https://stacks.math.columbia.edu/tag/00A7 and
   https://stacks.math.columbia.edu/tag/03DI. Pass.
4. The argument uses Mathlib's separation/local-injectivity and adjunction tools;
   unused helper imports are removed and the pruning claims are corrected.
   dag/units/sk-thm-picard-duality.json has empty realized lists and this item is
   not a unit-level realization. No unit or chapter route is changed. Pass.
5. The existing node now names both the faithful helper and the chosen-adjunction
   theorem. The new node matches its Lean signature, three proof steps and actual
   search digests; its source, construction dependencies and origin are recorded.
   Pass.

Changed in this second reading: proved the faithful helper completely; removed
its unused adjunction imports; removed letI and its linter suppression from the
item; repaired proof_deps, search records, the report and the unnecessary change
record. No existing signature or definition was changed.
