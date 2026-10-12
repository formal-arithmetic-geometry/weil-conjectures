## What changed

Proved `flat_adicCompletion_of_flat_local` in `Sheaf.RingTheory.FlatCompletion`, preserving its
signature. Constructed the completion map from compatible quotient maps with Mathlib's
`AdicCompletion.liftRingHom`, verified the levelwise characterization and the canonical-map
identity, and applied the existing `Module.Flat.flat_of_flat_quotients_powers` theorem.

Added the proved module `Sheaf.RingTheory.CompletionRestrictionFlatQuotients`, containing
`AdicCompletion.flat_quotients_of_flat_restriction`. It proves the quotient comparison of
steps 2–4 for any finitely generated ideal and any completion algebra flat over the original
ring. Its proof uses only Mathlib. Added proof-only imports of this module,
`Mathlib.RingTheory.AdicCompletion.LocalRing`, and
`Mathlib.RingTheory.AdicCompletion.AsTensorProduct`. Updated the parent DAG proof and added
the helper's node. The unit route is unchanged.

## Proved and sorry left

Closed one original hole: `flat_adicCompletion_of_flat_local`
(node `lem-weil-pbc-flat-completion`). Also proved the new theorem
`AdicCompletion.flat_quotients_of_flat_restriction`
(node `lem-weil-pbc-completion-restriction-flat-quotients`). Added zero holes, split off zero
unfinished statements. Neither delivered module contains `sorry`.

The existing imported `Module.Flat.flat_of_flat_quotients_powers` remains a dependency with
its own `sorry`, node `lem-weil-pbc-flat-module-powers`. No proof of a dependency was changed.
`AdicCompletion.isNoetherianRing` is used as an existing proved theorem, whose dependency
`MvPowerSeries.exists_surjective_toAdicCompletion` remains outside this delivery.

Both delivered modules compile locally in import order without warnings. The new quotient
lemma needs no local-ring or Noetherian hypotheses and includes n = 0; its proof handles
I = bottom, I = top, and zero target rings without additional assumptions.

## No longer needed

None: no original import was removed. Every original dependency is still used either in the
main proof or in the proved quotient helper. In the parent node,
`lem-weil-pbc-adic-completion-mod-power` and `lem-weil-pbc-flat-module-quotient-flat` move
under the helper node; they are not pruned from the argument. No unit statement or step,
node, or module has been bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically correct. It did not give a Lean construction of the
completion map or the transport between the ring and module quotient instances. This delivery
supplies both. No statement or definition was changed.

The local copies of `literature/stacks-project/more-algebra.tex` and `algebra.tex` are absent.
WANTED: those source files, Tags 0C4G, 05GG and 00HI, for the quotient helper node.
Read the official Stacks HTML of Tag 0C4G at https://stacks.math.columbia.edu/tag/0C4G.
Recorded `proof_origin.by = agent` for the Lean implementation. LeanSearch returned an
Internal Server Error for the new lemma; that search is recorded as unavailable without an
absence verdict, and Loogle, LeanFinder, and Mathlib source searches were used.

## New nodes

`lem-weil-pbc-completion-restriction-flat-quotients`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-completion-restriction-flat-quotients.json`,
realized by `AdicCompletion.flat_quotients_of_flat_restriction` in
`lean/Sheaf/RingTheory/CompletionRestrictionFlatQuotients.lean`. This is a proved, strictly
intermediate generalization of the quotient comparison: its conclusion is flatness only
modulo each power, not flatness of the full completion map. It has no `sorry` and relies only
on Mathlib. No change records are needed: existing signatures and public imports are unchanged.

## Second reading by H2

1. Interface: PASS. Read the full diff of FlatCompletion against the repository. The
   existing theorem signature is byte for byte unchanged; only its proof and three
   proof-only imports were added. No existing definition or public import changed.
   The quotient helper is a new theorem in its own module, with its own node.
2. Proof: PASS. Recompiled both modules in import order through lcompile.py with no
   errors or warnings. Searched both delivered Lean files for sorry and forbidden
   declarations; none occur. Scratch-copy #print axioms shows only propext,
   Classical.choice and Quot.sound for the helper. The original theorem additionally
   uses sorryAx from existing open dependencies (flat_of_flat_quotients_powers and
   the power-series surjection underlying isNoetherianRing). Thus its original
   local hole is closed, but it is not yet an axiom-closed target proof.
3. Intermediate statement: PASS. No unfinished statement was split off. Read the
   helper's complete natural-language proof and its Lean construction: evaluation
   identifies C/J^n with A/I^n, flat base change gives S/I^nS, and the representative
   formula transports the correct quotient action. For n = 0 both quotients are
   zero; I = bottom gives the original flat map for positive n; I = top makes C
   zero and a unital map C -> S forces S to be zero. A zero S is also harmless.
   Independent LeanFinder, Loogle and Mathlib grep searches with different queries,
   and searches through Sheaf and upstream RingTheory, found no direct existing
   theorem for this quotient comparison. The new proved helper is strictly a part
   of the original argument, not a restatement of completion-map flatness.
4. Route and pruning: PASS. The completion map is genuinely constructed from its
   compatible quotient maps. Its flatness proof takes Mathlib completion flatness
   and quotient base change first, then the existing flat-module-powers theorem.
   Every import supplies a signature or an actually used theorem/instance; all
   added imports used only by proofs are plain import. Compared the old proof_deps:
   completion-mod-power and flat-module-quotient-flat are now used by the helper;
   all others remain used. No node or module is bypassed. Read sk-thm-p1.json's
   realized statement and steps; this change is below that route and alters none
   of its realizations. No longer needed: none.
5. DAG: PASS. Read both delivered nodes and checked their proof steps, dependency
   unions and agent proof origins against the Lean. The helper's kernel/base-change
   dependencies are existing Mathlib leaves, not missing Sheaf declarations. Its
   node includes source, self-contained statement, searches, creation, blueprint,
   chapter/unit and Lean realization. The parent records construction, restriction
   flatness, the helper and the local flatness criterion in the same order as Lean.

Changes by the second reader: added this audit and recorded independent searches.
No Lean proof, statement, import or node needed repair. Closed one original hole
(flat_adicCompletion_of_flat_local), added zero holes, and split off zero unfinished
statements; the new helper flat_quotients_of_flat_restriction is fully proved.
