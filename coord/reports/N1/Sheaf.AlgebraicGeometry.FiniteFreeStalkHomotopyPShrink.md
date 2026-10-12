## What changed

Completed a compiling reduction of
`AlgebraicGeometry.Scheme.Modules.exists_shrink_homotopy_P_of_stalk` without changing
its signature, visibility, or original docstring. Added proof-only imports of
`Sheaf.AlgebraicGeometry.FiniteFreeReverseComponentsLift` and
`Sheaf.AlgebraicGeometry.FiniteFreeChainMapStalkEquality`.

The first theorem lifts arbitrary reverse-degree components without imposing differential
or homotopy equations. The second theorem detects equality of two fixed chain maps on a
smaller neighbourhood from equality of their stalk pullbacks. The main proof combines
these distinct steps: it identifies the lifted boundary with the prescribed difference
at the stalk using naturality and Mathlib's `nullHomotopicMap` identities, shrinks that
chain-map equality, constructs the null homotopy, and transports it through the natural
isomorphism from successive restrictions to direct restriction. The fully proved private
helper `homotopyOfNaturalIso` performs the final transport, including endpoint cancellation.
No definition contains a hole, and no arbitrary existence witness is used in a definition.

Updated the item's DAG proof, dependency list, and proof origin to match the Lean proof.
Added two new modules and their complete node records. No other existing module is adapted.
All three modules compile cleanly through `lcompile.py`; the main module takes about six
seconds against the compiled sandbox dependencies.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_shrink_homotopy_P_of_stalk`
(node `lem-pc-finite-free-stalk-homotopy-p-only`). The item's module now has no `sorry`.

Added exactly two named holes, each in its own new module:

- `AlgebraicGeometry.Scheme.Modules.exists_lift_reverse_components`
  (node `lem-pc-finite-free-reverse-components-lift`, module
  `Sheaf.AlgebraicGeometry.FiniteFreeReverseComponentsLift`).
- `AlgebraicGeometry.Scheme.Modules.exists_shrink_chainMap_eq_of_stalk`
  (node `lem-pc-finite-free-chain-map-stalk-equality`, module
  `Sheaf.AlgebraicGeometry.FiniteFreeChainMapStalkEquality`).

This is a decomposition: one upper hole closed, two lower holes added, net minus one hole.
It is not a claim that the theorem has a proof without `sorryAx` in its dependency closure.
Each remaining proof is exactly `:= by sorry`, with a complete finite-matrix proof in words.
The first has no fixed maps a,b or homotopy equations; the second has no homotopy data or
component lifting. Neither restates the main theorem.

## No longer needed

Removed the unused proof-only import `Sheaf.Topology.PresheafModuleStalkFunctor`
from the current repository version. No declaration from that module is used by this
reduction; the scalar germ arguments use Mathlib structure-sheaf stalks. This is an
import removed from this item, not a claim that the module leaves the whole target closure.

All three old direct `proof_deps` have been replaced in the item node:
`def-weil-pbc-free-module`, `def-weil-pbc-module-stalk`, and
`lem-weil-pbc-open-immersion-module-pullback-restriction`. Their mathematical ingredients
remain in the finite-matrix plans of the two new nodes, so no such node is claimed
pruned from the transitive argument. The parent pair-shrink,
stalk homotopy-spread, and chain-map lifting modules are not imported or used as shortcuts.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped with the original hole unchanged. Absence of a direct local
spreading lemma does not prevent a reduction: the geometric coefficient-lifting and
zero-germ steps can be stated separately, and the homotopy assembly is already in Mathlib.
The existing dependencies are definitions and restriction identifications, rather than a
ready-made theorem carrying out either finite matrix step. They do not directly close the
original theorem. This delivery makes those two missing steps precise and writes the
combination in Lean. The unit's local finite calculation route is preserved; its `realized`
lists are empty and no unit statement or step was bypassed or changed.

LeanFinder and Loogle searches of the main statement found homotopy constructors and
transport lemmas, rather than a stalk-spreading theorem. Searches for each new node found
free sheaf generators, ring spreading, or extensionality on all opens/all stalks, none of
which directly states the required local result. Local searches of both roots, all DAG
nodes, and Mathlib found no duplicate. LeanSearch returned Internal Server Error for both
new-node queries; their records report this as unavailable, without claiming a verdict.
The source-library finite free chain-map lifting modules were read: their differential
commutativity hypothesis does not apply to arbitrary reverse components. The pair-shrink
module depends on this item and would give a cycle.

Edge cases checked mathematically before stating the new lemmas: when d=0, every
reverse-degree component has a zero source or target, and only degree-zero map equality
remains; zero rank gives empty matrices; the zero complex has only zero maps; U=V is
allowed; no reducedness hypothesis is used, since equality of germs gives actual local
vanishing even over nonreduced rings. Empty intersections are the prescribed open. The
existential comparison e in the lifting theorem is a natural isomorphism on all complexes
on V, constructed by restriction/pullback comparison and pullback composition; this
naturality is needed on the fixed maps and is used in the main proof.

WANTED: the local copy of
`literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-perfect/lem-pc-perfect-locus.md`,
first two proof paragraphs, for the two new nodes. The listed file is absent on this
machine. The expansion follows the original node's numbered steps and its complete
finite-matrix docstring, both read in full. Its proof origin is explicitly marked as
agent-written; no claim of rereading the absent source is made.

Retry audit (2026-10-13): reread the saved reduction and all three node records.
Recompiled all three sandbox modules with `lcompile.py --all`: exit code 0,
with file times 17.4 s, 7.8 s, and 14.7 s. Retried the required
`deliver3.py N1 Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopyPShrink --no-push`: exit code 1,
before preflight, with the same ImportError for `refuse_missing` from
`tools/import_cycles.py`. Read-only inspection confirms that this checkout
defines neither `refuse_missing` nor `source_roots`, both imported by the launcher.
The project forbids workers from editing or bypassing these tools. The saved
proof and prior independent second reading are preserved; nothing was pushed.

## New nodes

`lem-pc-finite-free-reverse-components-lift` isolates steps 1 and 2 of the item's plan:
finite reverse-degree coefficient lifting, with a natural stalk comparison and exact
component equations, but no equation involving the differential. Its module is
`lean/Sheaf/AlgebraicGeometry/FiniteFreeReverseComponentsLift.lean`.

`lem-pc-finite-free-chain-map-stalk-equality` isolates the local vanishing portion of step 3:
finite matrices with zero coefficient germs become equal after shrinking. It applies to
arbitrary fixed endomorphisms of the twice-restricted bounded finite free complex, without
homotopy hypotheses. Its module is
`lean/Sheaf/AlgebraicGeometry/FiniteFreeChainMapStalkEquality.lean`.

Both inherit chapter `sec-picard-framework` and unit `sk-thm-picard-perfect`, have self-contained
statements and complete proof steps, and cite the same finite calculation source as the
item. No change record is required because no existing interface changed.

## Earlier second reading (a previous round; superseded)

1. PASS: compared the existing module with the current repository by diff, and
   mechanically checked that the existing theorem signature is byte-for-byte identical.
   Its visibility and original docstring also stay unchanged. The only changes are
   proof imports, a private proved helper, and the proof body. Both additional modules
   are new; no existing definition, target, or statement is changed.
2. PASS as a decomposition: compiled all three actual modules locally through
   lcompile.py without errors or warnings. Scratch copies with #print axioms show
   only propext, Classical.choice, Quot.sound for homotopyOfNaturalIso, and those
   three plus sorryAx for each public theorem. Exactly the two reported new public
   theorems have whole-proof sorry; there is no forbidden declaration or hollow
   definition. The lifted existential data are unpacked inside a theorem proof,
   never used to define an arbitrary object in the library.
3. PASS: reread both full new signatures and their finite-matrix docstring proofs.
   Boundedness makes the relevant degrees and reverse pairs finite; finite bases
   make their coefficient sets finite. Germ representatives lift coefficients, and
   zero germs vanish locally, including over nonreduced rings. Checked d=0, zero
   rank, zero complexes, U=V and empty coefficient sets. The comparison is natural
   on all complexes, as required by endpoint naturality in the main proof. Neither
   lemma asserts the original homotopy conclusion. Independent LeanFinder searches
   for local vanishing of finite-free maps and simultaneous extension of linear maps
   found scalar ringed-space vanishing and local generators, not either new theorem.
   Local searches found an etale constant-module refinement lemma, which uses a
   different site and stalk, and the downstream pair-shrink helper, which cannot be
   imported without a cycle. A Loogle query with NatIso was invalid and supplies no
   absence evidence. Neither geometric hole has a direct short proof from these APIs.
4. PASS: the proof follows the original finite calculation from the top: lift only
   reverse components, detect equality of their boundary and the fixed difference,
   then assemble and transport the homotopy using Mathlib. All public imports are
   needed for the signatures; the new imports are proof-only. Checked the unit's
   realized record (empty statement and step lists); no unit step or route is bypassed.
   Corrected the pruning report against the current repository, which now contains
   the unused stalk-functor import absent from the first worker's baseline.
5. PASS: read the three full node records, checked each lean.statement against its
   actual signature, and checked that the item's four proof steps follow the actual
   lifting, boundary computation, equality shrinking and natural-iso transport.
   Its proof_deps are precisely the two new nodes; their source, proof_origin,
   finite-matrix plans, searches, creation, chapter, unit and Lean records are present.
   The report candidly records that the cited blueprint text is unavailable locally.

Changed only this report: corrected the removed-import and replaced-direct-dependency
account, and recorded the independent second reading. No correct Lean proof was rewritten.
One original hole is closed by two new strictly narrower holes (net minus one); this
is a delivery of a decomposition, not an axiom-free proof of the original theorem.

Delivery tool failure: the second reader ran deliver3.py --no-push, but it stopped
before preflight in check_import_sources: ImportError cannot import name refuse_missing
from import_cycles (the repository tools/import_cycles.py). The launcher tool expects
refuse_missing and source_roots, neither defined by this checkout. No tool was edited
or bypassed, and nothing was pushed. Local compilation and explicit axiom checks above
completed successfully.


## Second reading by N1

Independent second reading on 2026-10-13 of the saved delivery and current repository.

1. PASS. Diffed the existing module against the repository and mechanically compared
   its theorem signature byte for byte, also matching every delivered theorem signature
   to its node's lean.statement. No existing interface, definition or docstring changed.
   Existing-node differences are confined to proof, proof_deps and proof_origin.
2. PASS as a decomposition. Recompiled all three modules through lcompile.py --all,
   exit 0, and compiled scratch copies with explicit #print axioms. The main theorem
   and the two new theorems use only propext, Classical.choice, Quot.sound and sorryAx;
   homotopyOfNaturalIso uses only the three permitted axioms. Exactly the two reported
   named theorems contain sorry, each as its whole proof. No forbidden declaration or
   hollow definition occurs; existential witnesses are eliminated inside a theorem proof.
3. PASS. Read both new signatures and complete matrix proofs. Finite support and finite
   bases make both coefficient lists finite. Stalk representatives lift entries; the
   germ equality criterion makes zero entries vanish locally, without reducedness.
   Checked d=0 (reverse components zero), zero ranks, the zero complex, U=V and empty
   coefficient lists. The lifting comparison is natural on all complexes, which is
   precisely what the endpoint calculation uses. Neither new theorem states the original
   homotopy conclusion. New independent LeanFinder queries about equal germs of finite
   free maps and simultaneous local-ring linear-map representatives found germ_eq,
   exists_const, local generators and ring spreading, not either complete statement.
   Read freeMatrix_pullback, pullbackFreeIso and the scalar germ API, and searched the
   local finite-free modules. The existing degreewise lift/shrink results concern
   same-degree maps of two complexes and differential defects; they are not direct
   instances of reverse-component lifting or equality of the fixed chain maps here.
   No short direct closure of either geometric lemma was found.
4. PASS. Read the main argument from its conclusion downward: direct-restriction
   transport, nullHomotopy/equivSubZero, chain-map equality shrinking, and reverse
   component lifting. The naturality and cancellation steps prove the fixed endpoints,
   rather than just some homotopic maps. Public imports supply signature types; the two
   new imports are proof-only. No unused extra import remains. No longer needed lists
   the removed stalk-functor import and all three replaced old direct proof dependencies.
   Read dag/units/sk-thm-picard-perfect.json: realized.statement and its step list are
   empty; the prescribed finite local calculation route is retained.
5. PASS. Read all three node records and their proof plans. The main node's four steps
   match the actual lift, boundary calculation, shrink and natural-isomorphism transport;
   its proof_deps are exactly the two new nodes. The new nodes have source, complete
   proofs, creation, blueprint, chapter/unit and verbatim Lean records. The unavailable
   blueprint source is acknowledged in the report, and origins are marked agent-written.

Changed only this report: added this independent reading and fresh verification.
The delivery closes exists_shrink_homotopy_P_of_stalk and adds the two explicitly named
holes listed above: one closed, two added, net minus one, a decomposition.
The old refuse_missing/source_roots import failure is now repaired in the supplied tools.
An initial dry run overlapped a separate local compilation and failed resolving a new
sandbox dependency; the retry is run alone after all compilation has finished.
