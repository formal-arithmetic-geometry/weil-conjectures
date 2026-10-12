## What changed

Proved `AlgebraicGeometry.exists_schemeHomDirectImageComparison` in
`Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` by explicitly transposing evaluation
through the fixed pullback adjunction, pullback tensor comparison and canonical
three-variable tensor-Hom family. The private generic helper proves the mate equation
on every test map and naturality in both entries. No comparison or adjunction data
was replaced by an arbitrary choice.

Proved `AlgebraicGeometry.schemeGlobalHomAdjunctionMap_isIso`, including both its
invertibility and naturality clauses, from `qcqsSheafRHomAdjunction`, the proved
coherator bridge and the existing Leray comparison. A private generic helper constructs
tensor-Hom adjunctions from the fixed natural bijections. Their hom equivalences give
exactly the mate equation required by `qcqsSheafRHomAdjunction`. Another generic
helper transports the natural sheaf comparison through Leray.

Added `Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections`, with the fully proved
`AlgebraicGeometry.dqCoherator_isIso_derivedGlobalSections`. It represents an arbitrary
derived map by a chain map between K-injectives, applies the existing chain-level
detection theorem, then transports invertibility through the quotient factorization
and right-derived units. Its proof has no new assumptions or holes.

All existing public definitions and theorem signatures are unchanged. Replaced the
obsolete REPAIR banner with a description of the existing pinned canonical data.
Isolated tensor-Hom naturality in a proved private theorem to avoid repeatedly copying
the large representative canonicality predicate into kernel proof terms. Specifying
the two monoidal instances explicitly in the generic comparison specialization
reduces unnecessary instance reconciliation; the final local compile took 41 seconds.

Validated the two modules together with `lcompile.py --all`, against the current
compiled library. All delivered lines are at most 100 characters. The generic
calculations were developed in scratchpad files outside the delivered Lean tree.
The source Tag 0B6I was read at https://stacks.math.columbia.edu/tag/0B6I because this
machine does not contain the referenced local Stacks TeX checkout.

## Proved and sorry left

Closed two of the four original holes:

- `AlgebraicGeometry.exists_schemeHomDirectImageComparison`
  (node `lem-pc-global-hom-adjunction`).
- `AlgebraicGeometry.schemeGlobalHomAdjunctionMap_isIso`
  (node `lem-pc-global-hom-adjunction`).

Also proved the new bridge
`AlgebraicGeometry.dqCoherator_isIso_derivedGlobalSections`
(node `lem-pc-dq-coherator-derived-global-sections`). No holes were added or split off.

The two original holes left unchanged are:

- `AlgebraicGeometry.exists_schemeGlobalSectionsDirectImageIso`
  (node `lem-pc-global-hom-adjunction`): underived identity on sections and its derived
  Leray comparison with the prescribed right-derived unit equation.
- `AlgebraicGeometry.exists_schemeHomTensorPullbackIso`
  (node `lem-pc-global-hom-adjunction`): invertibility of the canonical comparison
  characterized on K-flat representatives.

The proved declarations still rely on the named theorem holes of their dependencies,
as intended in stage 3. In particular `qcqsSheafRHomAdjunction` and the existing
K-injective coherator detection are used directly, not reproved or replaced.

## No longer needed

No mathematical dependency nodes are pruned: the unit route and the original
sheaf-Hom/coherator/Leray route remain. The direct proof import of
`Sheaf.AlgebraicGeometry.DQCoheratorAdjunction` is replaced by the proof import of
`Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections`, which imports it for its proof;
this removes no node from the target closure. All other original imports stay:
statement imports support the unchanged public signatures, and
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition` remains needed by
the outstanding Leray theorem's stated plan. No modules are claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The four-hole module already had the two repaired canonical definitions, despite its
REPAIR banner: `schemeHomPullbackAdjunction` uses the base-change pinned adjunction,
and `schemeHomTensorPullbackIso` chooses a uniquely specified comparison. No definition
repair was needed.

`exists_derivedDirectImage_internalHom_comparison` quantifies existentially over its
adjunction and tensor-Hom data. It cannot directly supply the fixed canonical equation
in this module. The new proof constructs that equation using the existing pinned
natural bijections; it does not identify arbitrary existential choices.

`dqCoherator_detects_globalSections` states the detection result only for chain maps
between K-injective representatives. The global theorem needs it for an arbitrary
derived morphism. The new bridge supplies that transport, with a complete proof.

The unit record `sk-thm-picard-duality` has empty `realized.statement` and step lists;
no realized unit node was bypassed. Every original dependency is retained.

## New nodes

`lem-pc-dq-coherator-derived-global-sections` records the proved bridge from existing
K-injective coherator detection to derived global sections of arbitrary derived
morphisms. It belongs to `sec-picard-framework`, unit `sk-thm-picard-duality`. The
statement assumes exactly the coherator adjunction and invertibility after DQ, not
quasi-coherence of either endpoint. The argument also covers zero objects and zero
maps whose DQ image is invertible. It uses the existing K-injective detection node,
Mathlib's K-injective localization bijection and the upstream representative theorem.
No new sorry or changed theorem statement is introduced.

Change record: `coord/changes/global-hom-adjunction-proof-helpers.md` documents the
private generic variable scopes which preflight classifies as an interface change.
These variables are section-local and the helpers are private; no downstream module
requires an adaptation. LeanSearch was also attempted and returned Internal Server
Error; that unavailable search is recorded alongside LeanFinder, Loogle and grep.


## Second reading by R3

1. Compared the entire item module with the repository using `diff -u` and the
   stage-3 declaration parser. Verdict: no existing public signature changed;
   `statement_changed` is empty. The seven existing definition bodies are unchanged.
   The only extra interface commands introduce scoped variables for private helpers,
   as documented in the change record. No target or definition was weakened.

2. Compiled both modules in import order using `lcompile.py --all`: no errors or
   warnings (6.8 and 40.1 seconds before the import repair). Read all private helpers,
   the evaluation-mate specialization, both clauses of the final theorem, and the
   complete K-injective bridge. Explicit `#print axioms` in scratch copies for
   `exists_schemeHomDirectImageComparison`, `schemeGlobalHomAdjunctionMap_isIso`,
   `schemeGlobalHomAdjunctionIso`, and `dqCoherator_isIso_derivedGlobalSections`
   shows only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from open
   dependencies. Exactly the two reported original named theorem holes remain;
   the bridge adds none. No forbidden declaration or hollow definition is present.
   The canonical tensor predicate fixes its data on K-flat representatives, and
   the mate equation fixes each comparison component by taking the identity test map.
   Representative choices in the bridge occur only inside a theorem proof.

3. No statement was split off with `sorry`. The one new, proved bridge is precisely
   the arbitrary-derived-morphism consequence of the existing chain-level detection
   theorem, rather than a restatement of global Hom adjunction. Read its hypotheses
   against Tag 0B6I's final paragraph, at
   https://stacks.math.columbia.edu/tag/0B6I: qcqs Y, any right adjoint DQ to inclusion,
   arbitrary endpoints, and invertibility after DQ suffice. Identity maps, zero objects,
   and a zero map with invertible DQ image are covered by the same cohomology argument;
   no endpoint quasi-coherence is silently assumed. Repeated concept searches with
   LeanFinder (K-injective localization and natural derived units), Loogle
   (`Functor.rightDerivedFunctorObjQIso`, no indexed match), and `rg` on both library
   roots found supporting tools but no existing arbitrary-morphism coherator theorem.
   Read the upstream K-injective representative theorem and Mathlib comparison node.
   The new node has the required source, proof, dependencies, origin, searches,
   creation, blueprint, unit/chapter and verbatim Lean statement fields.

4. The generic mate constructs a component from evaluation at the identity, proves
   its equation on every test map, then proves naturality. The tensor adjunction core
   uses the pinned bijections, so the final application supplies exactly the mate
   required by `qcqsSheafRHomAdjunction`. The bridge transports a represented chain map
   through quotient comparison and invertible derived units; Leray naturality then
   supplies the final naturality clause. No shorter exact library result was found.
   Checked `dag/units/sk-thm-picard-duality.json`: its realized statement and step
   lists are empty; the original coherator/Leray route is retained. Compared old and
   new proof dependencies: none of the old nodes is dropped, and the new bridge is
   added. No target-closure module is claimed pruned. The remaining Leray and K-flat
   existence holes require substantive constructions, not a short helper application.

5. Compared the existing node JSON diff and read the new node beside its proof.
   Verdict: only permitted proof/Lean fields change on the old node; its extra mate
   step and coherator transport describe the actual Lean proof. The union of each
   node's step uses equals its proof dependencies. The new bridge signature matches
   its Lean declaration verbatim, including the independent global-sections universe.

Changed the new bridge's `DQCoheratorAdjunction` import from `public import` to plain
`import`: no declaration from that module occurs in its theorem signature, and the
import is needed only by the proof. Updated the import description above. Kept all
correct proof terms and statements. Two original holes closed, zero holes added;
this is a net reduction of two local theorem holes, not a decomposition. No ledger
closure total is claimed before the maintainer's global verification.
