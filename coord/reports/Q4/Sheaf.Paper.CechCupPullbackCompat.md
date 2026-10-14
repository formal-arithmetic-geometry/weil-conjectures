## What changed

Completed the two remaining proofs in `lean/Sheaf/Paper/CechCupPullbackCompat.lean`:
`moduleCup_coefficient_naturality` and `moduleCup_pullback_naturality`.
Added proof-only imports of `Sheaf.Paper.ModuleCupCoefficientResolutionMaps` and
`Sheaf.Paper.ModuleCupPullbackResolutionMaps`. Their simultaneous resolution maps
already give the required section-pairing and class equations, so no split is needed.

Three proved private helpers establish surjectivity of computing-resolution class maps,
construct the paired kernel cocycle by Leibniz, and transport kernel cocycles through
additive maps between complexes over different rings. Every cycle's underlying section
is explicitly prescribed; no arbitrary data is chosen from an unproved existence theorem.
The sole existential eliminations occur in theorem proofs. The pullback proof has a
scoped heartbeat allowance for its three additive transports, matching the existing
substantial naturality proofs; the 60-second compile limit is unchanged.

Existing public signatures, definitions, visibility, public imports and docstrings are
unchanged. The existing node `lem-sc-picard-cech-cup-pullback-compat` now records the two
resolution-map dependencies and the complete cocycle arguments. The unit route is kept.

## Proved and sorry left

Closed both original holes:
- `AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`.

No `sorry` remains in the delivered module. No new holes, modules or DAG nodes are added.
This is a proof from existing declarations, not a decomposition. Existing imported
resolution theory may still depend on named holes; those are not changed by this delivery.

## No longer needed

None. Every original import is used by an existing statement or proof; the two new
imports are used by the completed naturality proofs. No node or module from the prior
route is bypassed. In particular the refinement comparison and cup resolution
representative dependencies remain needed by `cechCupPullbackCompat`.

## Where the brief, the DAG or earlier work was wrong

The prior node said that the sheaf-cup naturalities were unproved, but did not yet list
the already available coefficient and pullback resolution-map theorems as proof
dependencies. Those declarations suffice after explicit cycle and class transports.
No mathematical statement correction was needed.

LeanFinder, Loogle and Mathlib grep found general pullback/homology infrastructure,
not an existing Mathlib sheaf cup naturality theorem. Repository search found the two
resolution-map modules, both with the signatures needed here; import-direction checks
permit both imports. Sources read online because the local Stacks TeX is absent:
[Section 20.31](https://stacks.math.columbia.edu/tag/0FKU),
[Godement resolution](https://stacks.math.columbia.edu/tag/0FKS), and
[Cech compatibility](https://stacks.math.columbia.edu/tag/0FKV).

## Second reading by Q4

1. PASS — Read the whole delivered module and its diff against the repository.
   Every existing declaration signature is byte for byte unchanged; the declaration
   comparison also confirms unchanged visibility and docstrings, no removed
   declarations, and no public-import change. Only the two original theorem bodies,
   three private helpers, and two plain proof imports are added or changed. There
   are no changed existing definitions, target statements, or change records.
2. PASS — Compiled the delivered file with lcompile.py without errors or warnings
   in 37.3 seconds. A scratch copy with explicit `#print axioms` compiled in 37.9
   seconds. Both newly completed naturality theorems and all three new helpers use
   only propext, Classical.choice and Quot.sound, with no sorryAx. The unchanged
   cechCupPullbackCompat and cechRefinement_composition_naturality still inherit
   sorryAx from existing dependencies; the other public theorems use only the
   standard three axioms. The delivered source has no sorry or forbidden axiom,
   unsafe, opaque, implemented_by or extern declaration. The two private cycle
   definitions prescribe their underlying sections explicitly and prove their
   kernel membership. Existential resolution data and class representatives are
   eliminated only inside theorem proofs, never chosen to define new data.
3. PASS — No statements are split off and no new holes or nodes are introduced.
   Reviewed the surjectivity, Leibniz and additive-transport arguments, including
   degree zero, zero cycles, zero coefficient maps and different scalar rings.
   None needs positivity, flatness or a nonempty scheme. Repeated independent
   LeanFinder, Loogle and Mathlib grep searches with resolution/pairing and
   homology-surjectivity queries; no shorter applicable theorem was found. The
   repository has equivalent surjectivity and pairing-cycle helpers, but they
   are private in ModuleCohomologyCupProduct and ModuleCupRealizationEvaluation,
   hence unavailable through normal imports. The two public resolution-map
   theorems are used directly; neither assumes the desired cohomological cup
   naturality. Upstream source search found no matching resolution theorem.
4. PASS — The proofs reduce the original goals to already available computing
   resolution maps, lift arbitrary classes through epi/isomorphism composites,
   construct and transport the product cocycle, and rewrite the three class
   equations in the cup characterizations. All original imports remain needed
   by existing statements or proofs; both new imports are proof-only and used.
   Compared the old proof_deps: none is omitted, so `No longer needed: None` is
   complete. Read dag/units/sk-prop-av-cube.json and its route; neither its
   statement nor steps nor realized fields change (its existing realized lists
   are empty). No unit step is bypassed.
5. PASS — Only proof, proof_deps and proof_origin differ in the existing node.
   Its proof_deps is exactly the union of the proof steps' uses. Checked each
   dependency node's Lean record against the declarations used by the module;
   the two added dependencies name the resolution-map theorems actually used.
   Steps 6 and 7 describe the completed arguments accurately; the previous
   refinement/comparison route remains. No new-node obligations arise.

Second reading changed only this report, adding the independent checks and their
results. No Lean or DAG repair was needed. Closed two original holes, added zero
holes, and pruned no modules. The explicit axiom checks strengthen the first
report: both newly completed naturalities are free of sorryAx in the compiled
snapshot, although two previously proved declarations still inherit it.

Read the dedicated repair handoff in coord/returns/Q4.md. Its previous failure was
an imported duplicate symmetric-category instance during the axiom/sorry probe.
That failure does not reproduce in the current compiled snapshot: the whole
module, explicit axiom scratch copy, and deliver3.py dry-run probe all compile.
No upstream instance edit or consumer adaptation is needed. The dry run passed
preflight, classified CODEX because a node file changes and this is a returned
item. The required independent reading is recorded above.
