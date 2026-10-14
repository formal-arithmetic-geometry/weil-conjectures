## What changed

Repair of returned delivery X-d42bc (head d42bc58a6): removed the duplicate joint
statements RingHom.exists_limit_module_module_data_core and
RingHom.exists_limit_module_module_data. Their corrected statements were word-for-word
copies of RingHom.exists_limit_module_essentially_finite_presentation_over_system.
The existing joint theorem now contains the actual cofinal-tail restriction and
ring/module assembly proof. Its signature and visibility are unchanged.

The item retains the proved colimit-only declaration and least-tail helper.
The two separate ring and module construction obligations from the reviewed delivery
remain. DAG routes now follow the assembly in the existing theorem; retired duplicate
nodes refer to that declaration. No new duplicate statement is introduced.

## Proved and sorry left

Of the two original sorries, RingHom.exists_limit_module_module_data_colimit_part
(node lem-limit-module-colimit-part) is proved with its original signature.
RingHom.limit_module_tail_has_least (node lem-limit-module-tail-least) is proved.
RingHom.exists_limit_module_module_data_core is retired because its original
supplied-diagram assertion was false; this is not counted as a proof.
The wrapper RingHom.exists_limit_module_module_data is retired too.

RingHom.exists_limit_module_essentially_finite_presentation_over_system has a complete
Lean assembly proof from two strictly smaller construction obligations. There are no
sorries directly in the item. Two added construction sorries remain:

- RingHom.exists_limit_module_localization_ring_data, module
  Sheaf.RingTheory.LimitModuleLocalizationRingData,
  node lem-limit-module-localization-ring-data.
- RingHom.exists_limit_module_presentation_cokernel_data, module
  Sheaf.RingTheory.LimitModuleModuleDataConstruction,
  node lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-data.

This is one original-signature proof, one false-interface retirement, and a joint
construction decomposed into two obligations; no net sorry reduction is claimed.
No arbitrary data is defined from an unproved mere existence statement.
All four modules compiled locally. The delivery dry run with server compilation
enabled printed OK, pending only the independent second reading. The exact
import_prune_check.py check against a sandbox overlay containing all four repaired
sources returned exit 0 for every module, including the previously refused item.
The delivery tool rebased the packet on freshly fetched origin/sheaf-dag; nothing
was pushed.

## No longer needed

Retired duplicate declarations exists_limit_module_module_data_core and
exists_limit_module_module_data. The joint theorem no longer imports
Sheaf.RingTheory.LimitModuleModuleData or uses its colimit-only helper.
The item no longer imports LimitModuleLocalizationRingData,
LimitModuleModuleDataConstruction or Mathlib.CategoryTheory.Filtered.Final; these
proof imports move to the existing joint theorem, where they are used.

The old ring-data construction and its core (LimitModuleRingData and
LimitModuleRingDataCore; nodes
lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-ring and
lem-weil-pbc-limit-module-ring-data-core) are not used by the joint proof.
LimitModuleRingData remains publicly imported by the item to preserve its interface.
The colimit helper remains proved but leaves the joint theorem's import closure.
No unit-level statement or realized proof step is bypassed. The old dependency
lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module
and its former dependency
lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-core
are also no longer used as separate proof steps; their Lean records refer to the
existing joint theorem. Only LimitModuleModuleData leaves the target import closure:
LimitModuleRingData and its core remain reachable through the retained public imports
of the two construction modules, so their modules are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The previous reviewed delivery introduced two copies of the existing joint theorem.
The import-pruning landing check correctly refused these. Both copies are now retired,
and the existing theorem carries the proof itself. The earlier mathematical defects
and search findings are retained below for context:


E2: In the two-stage system `k → T=k[x]_(x)`, take `H=x` and `N=T/(x)`. The old fixed-tail
claim requires finite-dimensional `D₀` over k with `T⊗ₖD₀≅T/(x)`, impossible because the
left side is free while the nonzero right side has x-torsion. The repaired module lemma
can choose stage 1: `D₁=T/(x)`, so it asserts no such module at stage 0. This is the later
matrix stage of [Stacks Tag 00QX](https://stacks.math.columbia.edu/tag/00QX).

G1/E2: With constant base `F=k`, ring diagram `B=(k→T)`, and zero presentation, the old
hypotheses do not make `k→T` a localization. The repaired module theorem therefore
requires both exact localization predicates as named hypotheses. This example fails
`hRingTrans` and `hRingLimit` at stage 0. The joint theorem does not assume those predicates:
its new ring-only construction obtains a genuine localized polynomial-quotient diagram
from finite-presentation/localization data, following
[Stacks Tag 00QV](https://stacks.math.columbia.edu/tag/00QV).

H2 and A/F were repaired in the previous delivery. In this repair the corrected
joint core and wrapper are retired completely; their former assembly is now the
proof of the existing joint theorem. The change record quotes the original retired
interfaces, and the current imports and adaptation are recorded below.

B4/B9: The old module-data node used raw Lean as its mathematical statement, had a string
in `blueprint.from`, and silently changed the matrix stage in its proof. Those are repaired.
Blueprint searches `00QX`, `00QV`, `module directed` and `localization scalar` found zero
matching blueprint nodes; broader searches `cokernel` (18 hits) and `finite presentation`
(58 hits) contained no same-statement node. `same_as` is therefore empty. The recorded
ancestor of the existing module/core nodes is `thm-weil-pbc-finite-etale-lifting`; its
historical essential-surjectivity approximation step is refined by the limit-tower chain.
The ancestor tool on the core alone returned None because `created.item` is a module
name; the existing explicit ancestry and the successful ancestor lookup on the limit-tower
node provide the nearest blueprint ancestor used for the new records.

Searches: LeanSearch returned service unavailable (Internal Server Error), recorded
without a verdict. LeanFinder found localization finite-presentation preservation and
module cokernel APIs. Loogle had no `IsColimit` identifier in its service index; local
Mathlib search found the final-functor colimit equivalence used in the proof. Local rg
also checked the existing module diagram theorem: it assumes finite-type integer stage
rings and does not retain the supplied s-by-t presentation, so it does not discharge
this fixed-shape arbitrary-base module construction. The two construction obligations differ from the joint theorem; the duplicate joint
core and wrapper identified by the landing check are now removed.

## Forced adaptations

Sheaf.RingTheory.LimitModuleEssentiallyFinitePresentationOverSystem (unclaimed)
retains every existing signature and visibility. Original proof lines 147–156 refer
to the retired exists_limit_module_module_data, so the original fails against the
changed item. Replace its proof by the ring/module assembly and replace its single
proof import with the three modules used by that proof. No public import changes.
Counterfactual lcompile.py compilation of the original against the repaired overlay
fails at original line 152:4 with:

```
error(lean.unknownIdentifier): Unknown identifier `exists_limit_module_module_data`
```

The following rcases also fails because the application could not be elaborated.
The adapted module compiled in 6.2 seconds. The delivery tool repeats the baseline,
counterfactual and adapted checks and appends its complete compiler output.
No other existing module is adapted.

## New nodes

lem-limit-module-tail-least: proved elementary helper for the independent colimit.
lem-limit-module-localization-ring-data: ring-only polynomial quotient/localization
construction, with the transition and limit localization predicates.
lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-data:
presented module descent on an existential later tail, assuming the ring predicates.

Change records: coord/changes/exists-limit-module-module-data-core.md and
coord/changes/exists-limit-module-presentation-cokernel-data.md.

## Second reading by F2

1. PASS after metadata repairs. Compared both existing delivered modules with the
   repository using diff. The colimit-only theorem and the existing joint theorem
   retain byte-for-byte signatures and visibility. The only removed declarations
   are the false supplied-diagram core and wrapper, explicitly authorized and
   documented by exists-limit-module-module-data-core.md. Searches of lean/ show
   the joint theorem is their only outside caller. No target or definition changes.
2. PASS. All four modules compiled individually in import order through lcompile.py,
   with no errors or warnings. Scratch copies with #print axioms show no axioms for
   limit_module_tail_has_least and only propext, Classical.choice, Quot.sound for
   exists_limit_module_module_data_colimit_part. The two construction obligations
   and the joint assembly additionally use sorryAx. Text inspection finds exactly
   the two reported named-theorem sorries, and no forbidden declarations or hollow
   data. The assembly eliminates existence proofs only inside a theorem proof;
   it defines no public object by choosing an arbitrary unproved witness.
3. PASS. Read the two remaining construction statements and complete docstring
   arguments clause by clause against [00QV](https://stacks.math.columbia.edu/tag/00QV)
   and [00QX](https://stacks.math.columbia.edu/tag/00QX). The ring construction has
   no module input or output. The module construction takes a fixed ring diagram,
   chooses a later matrix stage, and only constructs its modules. Each is a strict
   part of the joint argument, not a restatement. Tested singleton systems,
   empty matrices (s=0 or t=0), and the two-stage k → k[x]_(x) example with H=x:
   the latter chooses stage 1 and does not assert impossible descent to stage 0.
   Prime contraction/locality and arbitrary-localization-to-prime replacement
   agree with the ring construction. Independent LeanFinder queries returned
   cokernel-presentation and localization-preservation APIs, not these diagrams;
   Loogle queries were rejected by its index/parser, so imply no search verdict.
   Local searches and reading of FinitePresentationColimit,
   FiniteRelationCokernelColimit, FiniteRelationMatrixLift,
   FinitePresentationModuleDiagram and FinitePresentationModuleBaseChangeDiagram
   found useful strict substeps, but no immediate proof of either full obligation.
   The latter two require finite-type integer rings, unavailable here. No remaining
   construction hole can be closed by a few-minute application of those statements.
4. PASS. The colimit-only assertion has the direct constant-diagram proof; Mathlib's
   connected constant-cocone theorem is an alternative but needs an extra import
   and connectedness instance. The joint proof uses two constructions, proves the
   tail inclusion final using Mathlib, transports its ring colimit, and pairs each
   restricted ring predicate with the corresponding module equivalence. All added
   assembly imports are proof-private. Public imports are unchanged or provide
   the signature APIs in new modules. The No longer needed list now distinguishes
   retired dependencies from the sole module removed from target reachability.
   Read dag/units/sk-thm-p1.json realized: neither the unit statement nor any of its
   realized steps is removed or bypassed; this is a lower-level construction.
5. PASS after repairs. Read all seven delivered nodes against their declarations,
   proof routes and old proof_deps. Existing assembly routes name exactly the two
   applied construction nodes, and the colimit route names its least-tail helper.
   The new construction nodes have source, full informal proof, searches, ancestry,
   chapter/unit and verbatim Lean signatures. Replaced the stale raw-Lean statement
   in the retired wrapper node by the unchanged mathematical joint-descent statement,
   removed stale statement-change metadata (the mathematical statement is unchanged),
   and added missing statement-definition
   dependencies and citations to the two construction nodes. Corrected the module
   name in the presentation-cokernel change record's Users table. Added independent
   search findings to the construction nodes. No Lean proof or signature was changed
   during this second reading.

Accounting: one original item hole is proved (colimit_part), one false original
item hole is retired (module_data_core), and two construction holes are added.
The existing joint theorem is a verified assembly over those two open obligations,
not an axiom-free completed proof. The least-tail helper is proved and adds no hole.
No positive net sorry reduction is claimed.

## Forced adaptations

### Sheaf.RingTheory.LimitModuleEssentiallyFinitePresentationOverSystem
Original against changed dependencies failed:
```
/tmp/forced-adaptation-fxb68tok/lean/Sheaf/RingTheory/LimitModuleEssentiallyFinitePresentationOverSystem.lean:152:4: error(lean.unknownIdentifier): Unknown identifier `exists_limit_module_module_data`
/tmp/forced-adaptation-fxb68tok/lean/Sheaf/RingTheory/LimitModuleEssentiallyFinitePresentationOverSystem.lean:150:9: error: Tactic `rcases` failed: `x✝ : ?m.1112` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-fxb68tok/.lbuild) [2.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
