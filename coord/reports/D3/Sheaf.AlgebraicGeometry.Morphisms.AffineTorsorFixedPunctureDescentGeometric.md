## What changed

Repair H9: `AffineTorsorSplitAction` now imports
`Mathlib.AlgebraicGeometry.Restrict` privately and drops the unused
`Mathlib.Algebra.Group.Action.Basic` import. The module compiles with these
minimal imports.

Corrected the false intermediate statement `AlgebraicGeometry.Scheme.affine_torsor_fixed_orbits_geometric`. Arbitrary m,K are replaced by `FixedOrbitData` for the action induced by the supplied splitting, and the conclusion includes projection compatibility over H. The second reader restored the original etale and unique-rotation torsor hypotheses, which the first worker had accidentally omitted. This is a statement repair, not a proof of the old false statement.

Added `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction`: deck maps, sections and their labels are constructed explicitly. `fixedPunctureDescentAction` uses a law theorem for proofs only. No object data are selected from a postponed existence theorem. The second reader proved `fixedOrbitData_of_action` using Mathlib orbit quotients, quotient representatives and stabilizers.

The geometric module publicly imports the action module because its public signature uses that action. `Mathlib.Data.Fintype.EquivFin` and `Mathlib.GroupTheory.GroupAction.Defs` are plain proof imports. All original public imports remain necessary for the public interface.

Change records: `coord/changes/affine-torsor-fixed-puncture-descent-geometric.md` and `coord/changes/fixed-orbit-data.md`.

## Proved and sorry left

Original holes closed: none. The original geometric statement is false and has been corrected, not proved. `AlgebraicGeometry.Scheme.affine_torsor_fixed_orbits_geometric` remains the named geometric descent hole, recorded by `lem-sbc-affine-torsor-fixed-puncture-geometric`, with the full sourced argument in its docstring.

Added hole: `AlgebraicGeometry.Scheme.fixedPunctureLabel_laws` in `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction`, recorded by `lem-sbc-affine-torsor-split-label-laws`. Its complete connected-summand and cocycle argument is in its docstring. This theorem supplies proofs of the laws of a concretely defined function.

Added and proved: `AlgebraicGeometry.Scheme.fixedOrbitData_of_action`, recorded by `lem-sbc-affine-torsor-fixed-orbit-data-of-action`. The first worker left this sorry; the second reader closed it. `AlgebraicGeometry.Scheme.fixedPunctureDeck_base` and `AlgebraicGeometry.Scheme.fixedSplitSection_base` also have complete proofs. There is no sorry in a definition. Two named holes remain across the two delivered modules; this delivery claims a statement correction and finite-orbit proof, not net progress in the original target closure or a completed descent proof.

## No longer needed

The unused `Mathlib.Algebra.Group.Action.Basic` import is removed, and
`Mathlib.AlgebraicGeometry.Restrict` is proof-only rather than public.
No module or DAG proof dependency is pruned. Arbitrary m,K are removed only
from the geometric interface; the existing `affine_torsor_orbit_data` in Core
is untouched. The action-law node is needed for the concrete action. The
proved orbit-existence node is available for future callers, but is not a
proof dependency of the geometric theorem, which receives orbit data as a
parameter.

The untouched Core and outer descent Lean and node copies have been removed from the delivery sandbox after confirming byte-for-byte equality with the repository and compiling them with the changed dependencies. Their source and records are not delivered.

## Where the brief, the DAG or earlier work was wrong

The old geometric interface admitted an empty product for a nonempty cover. The original Core source already has a certified counterexample and STATEMENT-DISPUTED marker for its arbitrary m,K interface. That source remains unchanged and does not invoke the geometric theorem. The report previously claimed that Core constructed the corrected orbit data and that the outer descent caller was adapted: neither claim was true, and both have been removed. The earlier return H2 is addressed by omitting the byte-identical outer descent node; H11 is addressed by these exact caller statements and the Users table.

The first worker's new geometric statement omitted etaleness and unique rotations. Counterexample: take H = R = Q, C = Q(sqrt(2)), trivial G, g = 1, and Y = T = Spec Q with identity cover and its one-component splitting. The first worker's hypotheses hold, the induced action has one orbit with trivial stabilizer, and its conclusion falsely identifies Spec Q with Spec C over Q. Restoring the original torsor assumptions excludes this example. No target statement is changed.

The geometric node now states the corrected mathematical assertion and has a statement_change record with its sole existing citer, `lem-sbc-affine-torsor-fixed-puncture-descent-core`, marked holds:false: its planned use cannot prove its already disputed arbitrary-orbit claim. No unheld caller correction is attempted. The unit `sk-prop-input-spreading` route is preserved; its realized fields are untouched (they are empty in the repository).

## Forced adaptations

Neither `AffineTorsorFixedPunctureDescentCore.lean` nor `AffineTorsorFixedPunctureDescent.lean` is changed. Neither invokes the modified geometric theorem. Both original sources compile against the changed action and geometric modules. No forced adaptations are needed.

## Statement corrected

The intermediate declaration `AlgebraicGeometry.Scheme.affine_torsor_fixed_orbits_geometric` was corrected because the old arbitrary `m,K` interface admits an empty product for a nonempty cover. The new statement supplies complete orbit representatives and exact stabilizers for the induced action, restores the etale and unique rotation hypotheses, and states compatibility over `H`. Its sole existing citer, `lem-sbc-affine-torsor-fixed-puncture-descent-core`, is marked `holds:false` because that caller retains the independently disputed arbitrary-orbit interface and does not invoke this declaration.

## Second reading by D3

1. Compared both delivered modules with the repository versions. Existing declarations retain their signatures except for the explicitly recorded correction of `affine_torsor_fixed_orbits_geometric`; the new action and orbit-data declarations are recorded in new nodes and the change records.

2. Compiled both delivered modules with `lcompile.py --all`. There are no errors or warnings. The only remaining `sorry`s are the named public theorems `fixedPunctureLabel_laws` and `affine_torsor_fixed_orbits_geometric`; no definition contains `sorry`, and the declarations use no forbidden axioms or modifiers.

3. Checked the new orbit-data and label-law statements against their constructions and source arguments. The orbit-data theorem is proved by finite orbit quotients and stabilizers. The label-law theorem is a strictly smaller connected-summand and cocycle statement with its proof sketch and node; neither restates the geometric target.

4. Checked proof routes and imports. The orbit proof uses Mathlib orbit relations, finite quotient enumeration, and stabilizers. The public action import is required by the geometric signature; `Restrict`, `EquivFin`, and group-action definitions are proof-only imports. No unit route is bypassed and no further pruning was found.

5. Matched the Lean declarations, nodes, proof dependencies, and change records. The corrected geometric statement and its counterexample are documented; the unit route remains unchanged. The only changes made during this reading were restoring the torsor hypotheses, proving `fixedOrbitData_of_action`, and adding this statement-correction and second-reading record.

## New nodes

`lem-sbc-affine-torsor-fixed-orbit-data-of-action`: the finite quotient construction is now proved from Mathlib `MulAction.orbitRel`, `Quotient.out_eq`, `Fintype.equivFin` and `MulAction.stabilizer`. It is strictly simpler than geometric descent and has no remaining hole. No exact duplicate of this project-specific data package was found.

`lem-sbc-affine-torsor-split-label-laws`: the identity and cocycle laws of the explicitly evaluated labels, with the concrete auxiliary definitions and two proved projection lemmas in the same new module. This is a smaller connected-summand argument, not a restatement of the geometric descent theorem. LeanFinder, Loogle and local searches found the relevant generic ingredients but no existing theorem for this construction.

Sources were checked against [Stacks 03SF](https://stacks.math.columbia.edu/tag/03SF) and [Stacks 0EYG](https://stacks.math.columbia.edu/tag/0EYG). The use of finite group orbits for connected Galois covers follows 03SF; the localization argument is supplied explicitly in the geometric docstring.

## Earlier second reading (a previous round; superseded)

1. Compared every sandbox module and existing node with the repository. The geometric signature changes intentionally and is recorded with its full old and new signatures. The new structure and action module are recorded separately. Core and outer descent sources and nodes were byte-for-byte unchanged and are omitted from delivery. No target or target definition changes.

2. Compiled all four original sandbox sources in import order after restoring the torsor assumptions and proving orbit existence. They compile without warnings. A scratch copy checks the axioms of every delivered theorem and definition: only propext, Classical.choice and Quot.sound, plus sorryAx for the two explicitly reported holes and the action whose law proofs use the label-law hole. No axiom, unsafe, opaque, implemented_by, extern or hollow definition occurs. The delivery tool also runs its full per-declaration probe.

3. Read the remaining geometric and label-law statements and their constructions. Restored the accidentally dropped torsor assumptions, gave the counterexample above, and expanded the geometric docstring into a complete descent/localization proof in words. Proved the finite-orbit split theorem rather than leaving it open. Searched Mathlib orbit quotients, stabilizers and finite enumerations and the local library using different queries; reused their existing ingredients. Scratch Lean examples check that d=0 forces m=0, that any trivial action has m=d, and hence that the trivial-group two-component case has m=2.

4. The corrected route still uses the induced action and exact stabilizers, then invariant-ring descent and localization. No shorter existing theorem was found for that combined geometric assertion. Proof-only imports are plain imports; public imports serve the public signatures and definitions. The No longer needed section records the complete pruning result, which is none. No unit step is bypassed, and the unit's realized fields remain unchanged.

5. Matched the geometric and new node signatures to the Lean declarations, corrected the geometric natural-language statement and proof plan, and recorded the existing Core citer's invalid planned use honestly. The finite-orbit node now describes the implemented quotient proof. New nodes identify their source, creator, chapter and unit. The unrelated outer descent record remains byte-for-byte unchanged and is omitted.

Changes during this reading: restored torsor assumptions; proved fixedOrbitData_of_action; expanded the geometric proof docstring; corrected the geometric statement/proof records and full change records; removed unchanged delivery files and contradictory report claims; added axiom and edge-case checks. The two geometric/action-law holes remain reported rather than counted as proved.
