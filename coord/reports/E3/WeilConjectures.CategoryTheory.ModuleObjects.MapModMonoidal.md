## What changed

Proved the six existing standalone balancing and linearity lemmas of
`WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal`. Every existing signature,
definition body, instance, comparison map, import, and docstring is verbatim unchanged.
The four balancing lemmas locally suppress unused-section-variable warnings to preserve
all their original hypotheses. No new declarations or modules are delivered.

The forward balancing equations use braiding and tensorator naturality. The inverse
balancing equations cancel invertible tensorators or the isomorphism on the scalar
factor. Linearity is checked after precomposition with the tensor-preserved coequalizer
projection and reduces to the defining action formula on the relative tensor product.
The transport proofs explicitly normalize `Functor.mapMod` before rewriting the action
with `modObjObj_smul`, avoiding transparency mismatches after the upstream sync.

The second reading repaired the earlier landing rejection: restored both
`mapModCoreMonoidal` and `comapCoreMonoidal` verbatim from the shared repository, removed
the two private unitor helpers used only in their withdrawn proofs, and withdrew the two
now-unnecessary change records. The complete sixteen-hole proof and its change records
are retained only under `scratchpad/`, outside the delivery. No consumer is adapted.

## Proved and sorry left

Closed 6 of the 16 original holes; added 0; split off 0. This is proof progress, not a
decomposition. The six proved declarations are:

- `CategoryTheory.Functor.mapMod_μ_balanced`.
- `CategoryTheory.Functor.mapMod_δ_balanced`.
- `CategoryTheory.Functor.mapModTensorIso_linear`.
- `CategoryTheory.Mod.tensorπ_comap_balanced`.
- `CategoryTheory.Mod.comap_tensorπ_balanced`.
- `CategoryTheory.Mod.comapTensorIso_linear`.

Ten pre-existing holes remain, unchanged in their original definition fields:

- `CategoryTheory.Functor.mapModCoreMonoidal.μIso_hom_natural_left`.
- `CategoryTheory.Functor.mapModCoreMonoidal.μIso_hom_natural_right`.
- `CategoryTheory.Functor.mapModCoreMonoidal.associativity`.
- `CategoryTheory.Functor.mapModCoreMonoidal.left_unitality`.
- `CategoryTheory.Functor.mapModCoreMonoidal.right_unitality`.
- `CategoryTheory.Mod.comapCoreMonoidal.μIso_hom_natural_left`.
- `CategoryTheory.Mod.comapCoreMonoidal.μIso_hom_natural_right`.
- `CategoryTheory.Mod.comapCoreMonoidal.associativity`.
- `CategoryTheory.Mod.comapCoreMonoidal.left_unitality`.
- `CategoryTheory.Mod.comapCoreMonoidal.right_unitality`.

No DAG node is attached to this module or these declarations. No new hole is introduced
inside a definition or anywhere else. The ten legacy field holes are not split-off
statements, and are not represented as newly proved results. Their complete reviewed
proofs are retained in `scratchpad/full-proof-reviewed.lean.txt`; this delivery omits
them because the current source-library gate forbids changing any non-theorem body.

## No longer needed

No library imports or old DAG proof dependencies were removed or bypassed; no library
module is pruned. The second reading removed the candidate's two private helpers
`CategoryTheory.Mod.tensorObjπ_leftUnitor_hom` and
`CategoryTheory.Mod.tensorObjπ_rightUnitor_hom` and their reassociated forms, which only
the withdrawn coherence proofs used. No helper remains unused in the delivered file.

## Where the brief, the DAG or earlier work was wrong

The first worker addressed the older upstream-sync failure, but the current return in
`coord/returns/E3.md` identifies a different rejection: the landing gate refuses changes
to the non-theorem bodies `mapModCoreMonoidal` and `comapCoreMonoidal` in the adopted
source library. Reading `tools/stage3_gate.py` confirms the unconditional restriction.
Change records do not exempt those edits. The full candidate passed `deliver3.py
--no-push` (commit `1c09990255`, classified CODEX), but that preflight does not remove
the later gate restriction. Delivering it unchanged would repeat the recorded rejection.
The final delivery therefore contains only the six theorem proofs, preserving both
constructors verbatim. The gate and all other project tools were left untouched.

Searches of `dag/nodes/` and `dag/units/` by module and principal declarations find no
attached node or realized unit step. The module follows its documented coequalizer
route; no mathematical statement error was found. The old module documentation's
“Sorried input” paragraph still describes all properties as open; this report gives
the precise current status without editing the source docstring.

## Second reading by E3

1. **Interfaces — pass.** Read the whole candidate and compared it against the current
   shared module with `diff`. After the repair, the final diff consists only of the six
   theorem proof bodies and four local linter settings. Existing signatures are byte for
   byte unchanged, including every original hypothesis; all definition bodies, data,
   instances, visibility, imports and docstrings are unchanged. No target or consumer
   statement is edited. Removed the candidate's two change records because neither
   constructor is changed in the final delivery.
2. **Proofs — pass for the six delivered closures.** Independently compiled the original
   complete candidate (4.0 seconds, clean) and a scratch copy with explicit `#print axioms`
   for all six lemmas, both comparison isomorphisms and both module isomorphisms, both
   constructors, and all three monoidal instances (5.2 seconds, clean): each used only
   `propext`, `Classical.choice`, and `Quot.sound`. Read every new proof. Balancing is
   the actual quotient condition transported by naturality; inverse balancing cancels
   isomorphisms; linearity cancels quotient epimorphisms, whose tensor-preserved
   instances are provided by `Symmetric`. No unproved witness choice, hollow data,
   forbidden construct, or new proof hole occurs. Recompiled and re-audited the final
   partial delivery after restoring the ten legacy coherence holes. Those holes now
   remain open explicitly as listed above, rather than being counted as proved.
3. **Splits and searches — pass.** No split-off statement or new declaration remains.
   Independently searched with a fresh LeanFinder query about quotient projections
   followed by unitors, and a Mathlib grep query about bimodule maps and unitor/coequalizer
   formulas. Results include concrete `ModuleCat` formulas, bimodule coequalizer lemmas,
   and Mathlib's `mapMod` TODO, but no replacement for the six generic theorem proofs.
   Searching `lean/` with alternative `unitor` and `tensorπ_leftUnitor/rightUnitor` names
   found downstream private or more specialized projection formulas, which cannot be
   imported here. The removed private helpers were true; none is needed in this delivery.
4. **Route and pruning — pass.** Read imported `MapMod`, `Symmetric`, and relevant
   `Monoidal` declarations. `MapMod` supplies functors/actions and the scalar-extension
   comparison; `Symmetric` supplies tensor-preserved quotient epimorphisms and associator
   formulas and publicly imports the monoidal structure used in statements and data.
   The equalizer-preservation import supplies the construction in the public
   `isColimitMapTensorπ` definition. No import is newly made public for a proof, no old
   proof dependency is bypassed, and no realized unit route changes. The six direct
   proofs use the existing quotient and coherence API without intermediate holes.
5. **Nodes — pass.** No node in `dag/nodes/` names this module or its principal
   declarations; no unit in `dag/units/` attaches a realized step to them. No delivered
   node, `proof_deps`, `proof_origin`, or unit record needs modification. The module's
   documented quotient construction matches the proof route.

Second-reading changes: restricted the delivery to the six standalone proofs so it
addresses the current recorded landing rejection; restored the two constructors;
removed their private helpers and change records; corrected the progress and remaining
hole lists; added independent search evidence and this review. Retained the complete
reviewed candidate outside the delivery for later use if the source-library restriction
is changed. Final standalone compilation passed in 2.9 seconds; the final explicit
axiom scratch audit passed in 3.8 seconds, with no `sorryAx` in any of the six closed
lemmas or their comparison isomorphisms. The prescribed dry run passed preflight at
`b772d7ad7d`, classified CODEX only because it repairs a returned delivery.
No whole-library build was run.
