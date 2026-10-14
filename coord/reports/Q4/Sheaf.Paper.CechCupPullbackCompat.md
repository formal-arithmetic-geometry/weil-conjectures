## What changed

Completed the two remaining proofs in
`lean/Sheaf/Paper/CechCupPullbackCompat.lean`:
`AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality` and
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`.
Their signatures, visibility, and existing docstrings are unchanged.

Added proof-only imports of `Sheaf.Paper.ModuleCupCoefficientResolutionMaps`
and `Sheaf.Paper.ModuleCupPullbackResolutionMaps`. Both import directions were
checked with `tools/import_direction.py may`; neither creates a cycle.
These existing declarations supply simultaneous computing pairings, strict
cochain pairing equations, and the three cohomology-class equations.

The new private helpers prove that computing resolution classes are surjective,
construct a product kernel cycle using Leibniz, and explicitly transport a kernel
cycle along an additive cochain map across possibly different scalar rings.
The coefficient proof uses the existing same-ring cycle transport. In both
proofs, lift the two arbitrary cohomology classes, form their product cycle,
transport all three cycles, apply the strict pairing square, and combine the
source and target `IsModuleCupProduct` characterizations with the three class
identities. The construction uses no additional isomorphism, flatness, or cover
hypothesis. Zero coefficients, zero morphisms, degree zero, and empty schemes
use the same kernel and additive-map formulas.

Updated only `proof`, `proof_deps`, and `proof_origin` of
`lem-sc-picard-cech-cup-pullback-compat` to record these arguments and existing
dependencies. The unit route is unchanged; its Čech comparison and refinement
steps remain in the module.

Searches: LeanFinder for sheaf cup coefficient/pullback naturality returned
group-cohomology facts, not this result; Loogle found `HomologicalComplex.cyclesMap_i`;
Mathlib grep for cup naturality returned no hits. Searches in both library roots
found the two computing-resolution map theorems used here. Their Lean signatures
and nodes were read. The cited local Stacks source is not present on this machine;
Stacks Tags 0FKS, 0FKU, and 0FKV were read on the official Stacks website.

Validation: `lcompile.py` compiled the complete module cleanly in 38.5 seconds
and the repaired support module in 36.5 seconds, both below the 60-second limit.
The updated node closure has no missing dependencies or cycles (675 reached
nodes), and every delivered Lean line has at most 100 characters. A non-module
import probe against the original shared build reproduces the recorded collision
in 1.4 seconds; against the delivered artifacts it succeeds in 2.2 seconds.
`#print axioms` for both new naturality proofs lists exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## Proved and sorry left

Closed both original holes, by declaration name:

- `AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`.

No `sorry` remains in the delivered module. No holes or public intermediate
statements were added; zero split-offs. These proofs use existing library
resolution-map theorems and retain their recorded transitive proof dependencies.
Both completed naturality declarations have only the three permitted axioms.
This delivery does not claim to remove other holes in their imported modules.

## No longer needed

None. Every original import supplies a statement, definition, or proof used by
one of the retained declarations. No existing DAG branch or module is pruned.
The two added imports are used by the two new proofs.

## Where the brief, the DAG or earlier work was wrong

The existing node describes the sheaf-cup naturalities as still unproved. Its
proof and proof-dependency fields now record their completed proofs. The existing
compatible computing-resolution declarations suffice, so no further split is
needed. No mathematical statement or definition was changed.

The dedicated repair entry in `coord/returns/Q4.md` records a duplicate anonymous
local instance name in the cup-product import closure. An inherited sandbox
repair of `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` addresses it by naming
its seven local instance auxiliaries. Their types, bodies, priorities, and local
visibility are unchanged; no mathematical theorem is weakened or strengthened.
The module is unclaimed. The change record is
`coord/changes/Q4-module-cup-compatibility-instance-names.md`.

## Forced adaptations

The support module is an unclaimed repair, rather than an adaptation of a held
module. The original failure reported in the dedicated return was:

```text
import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility failed, environment already
contains AlgebraicGeometry.Scheme.Modules.instSymmetricCategorySheafOfModulesOpensCarrierCarrierCommRingCatToRingedSpaceModuleRings_1
from Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization
```

The only changed lines in this support module assign unique names to its seven
local instance declarations (CommRing, MonoidalCategory, SymmetricCategory,
HasColimitsOfSize, MonoidalPreadditive, MonoidalClosed, and
HasFunctorialFlatResolution). This fixes the import-name collision before the
axiom/sorry probe can run. No proofs, instance values, mathematical signatures,
or downstream modules are changed.



## Second reading by Q4

1. **Interfaces: PASS.** Independently diffed both delivered modules against the
   repository. The seven existing public theorem signatures in the item and the
   support module's public theorem signature are byte-for-byte unchanged. The
   support diff only names its seven formerly anonymous local instances, with
   identical types, values, priorities and visibility; its change record explains
   the dedicated return. No existing mathematical definition changed.
2. **Proofs and trust: PASS.** Independently compiled both complete modules with
   `lcompile.py --all`: 37.6 s and 36.2 s, clean, below the per-file limit. Neither
   delivered source contains `sorry` or a forbidden declaration/attribute. A fresh
   scratch copy of the actual item, with `#print axioms` for all seven public
   theorems, compiled in 33.8 s. Both newly completed naturalities use exactly
   `propext`, `Classical.choice`, `Quot.sound`. The existing comparison theorem and
   refinement-composition theorem also report `sorryAx` from their still-open
   imported comparison dependencies; the other three existing naturalities use
   only the permitted axioms. The new additive cycle is explicitly constructed
   from the cochain map and its chain equation, not chosen from a holed existence
   theorem. The computing pairings are destructured only inside theorem proofs.
3. **Split-offs and edge cases: PASS.** Zero new holes, zero split-off statements,
   zero new public intermediate statements. Read the existing coefficient and
   pullback resolution-map interfaces, `CupAcyclicResolution.class`,
   `CupResolutionPairing.leibniz`, and `IsModuleCupProduct`. The proof uses all three
   supplied class equations and the strict pairing identity in the correct
   directions. Kernel membership follows from Leibniz and the two zero
   differentials, including p=0 or q=0. Zero coefficients/maps and the empty
   scheme require no nonzero or nonempty hypothesis. The scalar-changing helper
   uses only additivity, so it does not presume a common coefficient ring.
4. **Route, searches and pruning: PASS.** Read the full item from its comparison
   theorem downward. Independent LeanFinder search for induced bilinear homology
   naturality, Loogle search for homology maps, and Mathlib grep found the standard
   cycle/homology naturality facts already used, not a shorter cup theorem. Local
   searches found matching surjectivity/product-cycle helpers only as private
   declarations in other modules; no public API can replace these local helpers.
   All original direct imports serve retained statements, definitions, or proofs;
   both added imports are proof-only and used. No old proof dependency is pruned.
   The existing unit record `sk-prop-av-cube` is unchanged (its `realized` entries
   are empty in the repository); the comparison, refinement and cup steps remain.
5. **DAG: PASS.** The only changed node fields are `proof`, `proof_deps`, and
   `proof_origin`. The new steps faithfully describe the two actual reductions;
   `proof_deps` equals the union of their recorded step dependencies. Read the
   existing dependency declarations rather than introducing replacement nodes.

Second reading changed no delivered Lean or DAG: the proof and instance-name
repair are correct. Added this independent review and regenerated the scratch
axiom check from the delivered source (the inherited scratch copy was stale).
Net delivery: two original holes closed, no holes added, no modules pruned.
