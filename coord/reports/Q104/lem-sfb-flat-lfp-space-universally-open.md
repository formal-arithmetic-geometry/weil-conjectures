## Maintenance resolution, 2026-10-23

The historical reachability return for immutable head `90b473dc935d` is
superseded by the current DAG. The item is now reached from a current target
through the nodal-curve-stack route. Its helper
`def-sfb-space-morphism-properties`, cited in the item's `stmt_deps`, is therefore
also reached. The retained `import_flags: ["unreachable"]` was stale and
contradicted current reachability, besides being a maintainer-owned field
forbidden on a new stage-2 definition node.

Maintenance removed only that stale field from the helper JSON. Both Lean
modules, every declaration/signature, the item's statement and proof, all
source/search records, and all dependency edges are retained. The helper remains
a NEW definition node of this delivery; no prerequisite or Lean binding was
pre-landed. This is a data correction on the current graph, not a tool bypass.
The normal preflight and actual `nt_incremental2.check` landing rule are used
unchanged. The historical BLOCKED/retry appendices below describe the old base;
do not restore the obsolete flag from them or the old return.

Resume the retained packet on current `sheaf-dag`; run the normal dry run and
deliver for independent review. Maintenance does not clear the return or claim,
approve stage 2, or push a delivery branch.

## Worker report

Item: lem-sfb-flat-lfp-space-universally-open. The module
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen` states
`AlgebraicGeometry.AlgebraicSpace.universallyOpen_of_flat_of_locallyOfFinitePresentation`.
Its only proof is `by sorry`. The accompanying definition module has real predicate
bodies and no postponed data or theorems.

I read the complete item, its proof, all seven statement-dependency nodes, and the
signatures/docstrings of their recorded declarations. I also read the three scheme
proof dependencies and their Mathlib declarations. Source checked locally:
`literature/stacks-project/spaces-morphisms.tex`, Tag 042S (lemma-fppf-open,
lines 5879–5903), Tag 03MM (lemma-flat-local, especially (7)), Tag 0410
(lemma-finite-presentation-local, especially (7)), definitions P, separated,
locally-finite-type, locally-finite-presentation, flat, open, closed and proper.
There is no repair note for this item. The example CompactObject module is withdrawn;
its node points to the upstream module, whose public namespace conventions are followed.

Clause-by-clause correspondence:

* Algebraic spaces in the convention of def-trf-algebraic-space: binders
  `{S : Scheme.{u}} {X Y : AlgebraicSpace S}` and `(f : X ⟶ Y)`. These are the
  existing full subcategory of fppf sheaves with representable diagonal and a
  representable surjective etale scheme atlas; morphisms are natural transformations.
* The size convention: explicit `universe u`, schemes and test fields in `u`, the
  existing presheaves with values in `Type u`, and their existing point classes in
  `Type (u + 1)`. All test schemes and base-change spaces use this same universe;
  no independent smaller universe can make a chart hypothesis vacuous.
* Flatness: `hf : MapIsFlat f`, whose body is `MapIsLocally (@Flat) f`.
  `MapIsLocally` quantifies over every pair of scheme charts `a,b`, with
  `IsEtale a`, `IsEtale b`, and the equation
  `a ≫ f.hom.hom = yoneda.map h ≫ b`, and concludes `Flat h.left`.
  This is exactly the all-compatible-chart reading in 03MM(7), explicitly permitted
  by the item's proof. It does not require that `f` be representable.
* Local finite presentation: `hlfp : MapIsLocallyOfFinitePresentation f`, with
  exactly the same chart test and `LocallyOfFinitePresentation h.left`, as in 0410(7).
  There is no global finite-presentation, quasi-compactness or separation assumption.
* The properness convention in the introductory text is supplied by `MapIsProper`,
  rather than imposed as an extra hypothesis. Its three conjuncts are
  `MapIsSeparated`, `MapIsFiniteType`, and `MapIsUniversallyClosed`.
  Separatedness uses `IsRepresentableWith` closed scheme immersions for
  `pullback.diagonal f.hom.hom`. Finite type uses the existing
  `MapIsQuasiCompact` and the chart test for `LocallyOfFiniteType`.
  Universal closedness quantifies over every `Y' : AlgebraicSpace S`,
  `g : Y' ⟶ Y`, and asserts `IsClosedMap` of the canonical point map of the
  second sheaf-pullback projection. Thus it uses algebraic-space base changes.
* Universal openness: the first conclusion, `MapIsUniversallyOpen f`, unfolds to
  `∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
  IsOpenMap (mapPoint (Limits.pullback.snd f.hom g.hom).hom)`.
  The sheaf pullback is an algebraic space by the existing fibre-product theorem;
  its presheaf's `Point` and `pointTopologicalSpace` are the existing point space
  and topology. No underlying topological-fibre-product identification is assumed.
* Quotient topology: `pointTopologicalSpace` is final for all representable etale
  scheme-source maps. Its docstring identifies this with the quotient topology
  of any surjective etale atlas. I read `points_atlas_isOpen_iff` in
  `AlgebraicSpaceEtaleOpenImage`, which explicitly states that equivalence. No
  new topology, choice of atlas, or topology hypothesis is introduced here.
* Whole image open: the second conjunct `IsOpen (pointImage f.hom.hom)` uses the
  existing image set defined by field-valued point representatives. It is exactly
  `|f|(|X|)`, including the empty-source case.

Dependency declarations used (all names below are in namespace AlgebraicGeometry,
with AlgebraicSpace names qualified further as indicated):

* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsRepresentableWith`.
* `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` and its stalk equivalence
  `Flat.iff_flat_stalkMap` read to check def-weil-flat-morphism.
* `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `.Separated`, `.UniversallyClosed`:
  `IsProper`, `IsSeparated`, `UniversallyClosed` read for the scheme conventions;
  the space predicates use representability of the diagonal and universal point-map
  closedness rather than the scheme-only classes on a space morphism.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact` read for finite-type convention.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. The conclusions use its sheaf fibre product,
  and the proof docstring uses its atlas base-change and point-lifting content.
* `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses` and
  `.AlgebraicSpacePointTopology`: `AlgebraicSpace.Point`, `PointRepresentative`,
  `PointRepresentative.Rel`, `schemePointMap`, `pointTopologicalSpace`, `pointImage`.
* `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint` and
  `MapIsQuasiCompact`, reused verbatim. I also read `MapToSchemeIsLocally`,
  `MapToSchemeIsSeparated` and `MapToSchemeIsUniversallyClosed`: those accept only
  scheme targets, so they cannot state the general arbitrary-space assertion.
  `scompile.py --source` confirmed that module's current server source.
* Proof-only imports: `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
  (`UniversallyOpen.of_flat`, `Scheme.Hom.isOpenMap`), and
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (`etale_comp`, `Etale.of_comp`,
  the open-immersion instance). These implement the three recorded scheme proof
  dependencies; the algebraic-space and flat/lfp proof dependencies already enter
  through the public definition-module imports. No proof import is omitted for a cycle.

Edge cases checked mathematically before writing: empty source, empty target (then
source empty), empty open subset, identity morphism/base change, arbitrary non-scheme
algebraic-space base change, non-quasi-compact or nonseparated source, and arbitrary
characteristic. Empty images are open; the identity base change gives the whole-image
clause. Neither atlas surjectivity nor representability of f is added as a hypothesis.
The definitions of properness retain their full global content but are not hypotheses
of this theorem. There are no node faults and no STATEMENT-DISPUTED flag.

Searches (all msearch output logged in sandbox searches.jsonl):

* LeanFinder: `A flat locally finitely presented morphism of algebraic spaces is
  universally open`: 8 hits, led by the scheme-only `UniversallyOpen.of_flat`.
* Loogle: `AlgebraicGeometry.UniversallyOpen, AlgebraicGeometry.Flat,
  AlgebraicGeometry.LocallyOfFinitePresentation`: the scheme-only instance above.
* Mathlib grep: `AlgebraicSpace|UniversallyOpen.of_flat` in AlgebraicGeometry:
  one hit, UniversallyOpen.lean:147, again scheme-only.
* LeanSearch: `Flatness local finite presentation proper and universally open
  morphisms of algebraic spaces tested on etale scheme charts`: 8 scheme-property
  hits; none define the missing general space notions.
* LeanFinder: `Definitions of flat locally finitely presented proper and universally
  open morphisms of algebraic spaces on etale scheme charts`: 8 scheme-property hits.
* Mathlib grep: `MapIsLocally|MapIsFlat|MapIsProper|AlgebraicSpace`: zero hits.
* Project rg of `AlgebraicSpace` and this item's id in `lean/WeilConjectures`:
  no matching space framework/theorem; NoetherianComponents' similarly named
  universal-openness theorem has scheme binders, so is not this statement.
* Project rg of chart/flat/finite-presentation/proper/universal-open definitions in
  `lean/Sheaf`, and exact proposed names in `dag/lean_names_upstream.json`:
  only existing scheme-target helpers, point definitions, and chartwise etaleness.
  Those ingredients are reused. No exact general definition or theorem exists.
* Parsed all DAG definition statements containing algebraic spaces and the relevant
  properties, and searched for the proposed node id. No duplicate general node.
  `tools/blueprint_refs.py search space-morphism-properties`: zero matches;
  `ancestor` reports the inherited `blueprint.from.node = None`.

Validation: `scompile.py Q104 lem-sfb-flat-lfp-space-universally-open` compiled both
modules separately and together in dependency order, against the live server build,
with no errors or warnings. No local Lean or global build was run.

## New nodes

`def-sfb-space-morphism-properties`, in the item's chapter and unit, adds just the
missing general algebraic-space morphism properties. The predicates are written in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`. Their sources are the
Morphisms of Spaces definitions and Tags 03MM(7), 0410(7), read as detailed above.
The node cites the existing algebraic-space, scheme-property, point-topology,
proper-curve-moduli point-map/quasi-compactness, and fibre-product nodes. Searches
found only scheme predicates and scheme-target specializations, so those are reused
and the general chart tests, separatedness, finite type, properness and universal
openness/closedness are supplied here. `MapIsLocally` is the explicit chart-test
predicate, not an unsupported assertion that an arbitrary scheme property is etale local.
All eight declarations carry this new node's blueprint/source docstrings. The inherited
null blueprint ancestor and full via chain are retained with the item prepended.
The original item changes only in `lean` and addition of this definition node to
`stmt_deps`; its mathematical statement and proof are unchanged.

## Returned delivery repair

Return L, immutable head `90b473dc935d`: incremental DAG validation found that
`def-sfb-space-morphism-properties` is not reached from a target and lacks the
`unreachable` flag. Added `import_flags: ["unreachable"]` to this new definition
node, as required by the return and stages/1-dag.md. The item still cites the new
node in `stmt_deps`; its statement, signatures, and both Lean modules are retained.
The initial saved-packet dry run passed compilation and preflight at `4929b798ecb`;
this metadata repair addresses the additional independent-review finding.

Repair self-check: read the current main DAG and overlaid the two sandbox node
records, then used `dag_queue.Dag.distances_from` with current and former targets
(the reachability calculation used by the validator, without running check_dag).
Both the item and the new definition are outside that reach. The new definition
now has `import_flags: ["unreachable"]`, satisfying the returned condition.

Tool failure: the repaired packet's prescribed `deliver2.py --no-push` exits 1:
`(b) new node def-sfb-space-morphism-properties: key(s) outside the rule:
import_flags (the maintainer's fields come with the merge)`. The saved packet
without the flag passed dry run, but failed independent incremental DAG review;
the packet with the required flag is refused by preflight. No launcher script,
project tool, live file, or Git state was directly modified. No push was attempted.
The maintainer must permit this repair field or apply the flag during merge before
incremental DAG validation. Lean source is unchanged from the clean initial dry run.

## Repair retry 2026-10-22

Inspected the retained report, both node records and both Lean modules before
running the required saved-packet dry run. Compared the item against the current
read-only main DAG: only `lean` and `stmt_deps` differ; the new definition node
is still absent from main. The retained new node already contains the exact
reachability repair requested for immutable head `90b473dc935d`, namely
`import_flags: ["unreachable"]`. No mathematical statement or Lean source needed
changing for this return.

Reproduced the tool failure with
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
It exits 1 with:
`(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`.
The tool explicitly reports `PREFLIGHT FAILED, nothing pushed`. Removing the flag
would restore the independent-review reachability defect, so the required flag
is retained. No launcher scripts, live files or Git state were directly modified.
The prescribed delivery gate must permit the returned repair or apply its
maintainer-owned flag before incremental DAG validation.

## Saved-packet repair verification 2026-10-22 09:42 UTC

Ran the prescribed saved-packet `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push` before making changes. The wrapper checked both Lean files on the server, staged the packet, and exited 1 at stage-2 preflight with exactly one reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

It explicitly reported `PREFLIGHT FAILED, nothing pushed`. The required returned-head repair, `import_flags: ["unreachable"]`, is already present and is retained. Compared the packet with current read-only main without Git commands: the item differs only in `lean` and `stmt_deps`, and the new definition node is absent from main. No Lean or node content was changed on this retry. Removing the flag would undo the requested repair; patching or bypassing the gate is forbidden by the launcher instructions. Delivery therefore requires the maintainer-owned gate to accept or apply this reachability flag.

## Saved-packet repair verification 2026-10-22 09:44 UTC

Ran the required initial saved-packet dry run using the prescribed, unmodified
`deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
It checked both Lean files on the server and exited 1 at preflight:
`(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`.
It reported `PREFLIGHT FAILED, nothing pushed`.

Compared the retained packet to current read-only main using JSON reads: the
item differs only in `lean` and `stmt_deps`; the new definition remains absent
from main. The item cites it and its required `import_flags: ["unreachable"]`
is present. This repair remains incompatible with the prescribed delivery gate.
Removing it would undo return L; modifying or bypassing the gate is expressly
forbidden. Retained all Lean and node content, made no direct Git mutations,
and did not push. The gate must accept or apply this maintainer-owned flag.

## Saved-packet repair verification 2026-10-22 09:47 UTC

Ran the required saved-packet dry run before changing anything:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
It checked both Lean files on the server and rejected the packet with one reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

The wrapper reported `PREFLIGHT FAILED, nothing pushed`. Read both retained Lean
modules and compared the sandbox nodes with current main by JSON reads: the new
definition remains absent, the item's only changed fields are `stmt_deps` and
`lean`, and the new node retains `import_flags: ["unreachable"]`, the repair
required by return L at immutable head `90b473dc935d`. No mathematical or Lean
change is required by that return. Removing the flag would undo the requested
repair; the launcher expressly forbids modifying or bypassing the gate. Retained
the repaired packet without changing Lean or node content. Delivery is blocked
by the prescribed gate's refusal of the required reachability metadata.

## Saved-packet repair verification 2026-10-22 09:50 UTC

Ran the required initial saved-packet dry run with the unmodified prescribed
`deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
The wrapper checked both Lean files on the server, staged the packet, and exited 1:

```text
preflight FAILED (stage 2), 1 reason(s); do not push:
 (b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

It reported `PREFLIGHT FAILED, nothing pushed`. Read both retained Lean modules
and compared both node records against current read-only main by JSON parsing:
the item differs only in `lean` and `stmt_deps`, the new definition remains absent
from main, and it retains `import_flags: ["unreachable"]`, the precise repair
required by return L for immutable head `90b473dc935d`. The dry run refreshed its
own delivery base through the authorized wrapper. No Lean or node changes are
needed for the returned finding. Removing the flag would undo it; modifying or
bypassing the launcher gate is explicitly forbidden. Retained the repair and
recorded this concrete tool refusal. No push, direct Git command, or live edit
was performed. The gate must permit or apply the required reachability metadata.

## Saved-packet repair verification 2026-10-22 09:54 UTC

Ran the required saved-packet dry run before changing the packet, using the prescribed unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server, refreshed its delivery bookkeeping, staged the five delivery files, and exited 1 with exactly one preflight reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

The wrapper reported `PREFLIGHT FAILED, nothing pushed`. Read both retained Lean modules and compared the node records to current read-only main by JSON reads: the new definition is absent from main; the item differs only in `lean` and `stmt_deps` and cites the new definition. The definition retains `import_flags: ["unreachable"]`, as required by return L at immutable head `90b473dc935d`. Removing the flag would undo the requested repair. No Lean or node content was changed, no direct Git commands or live edits were performed, and no push was attempted. The prescribed gate must accept or apply this required reachability metadata; modifying or bypassing it is forbidden by the launcher instructions.

## Saved-packet repair verification 2026-10-22 09:56 UTC

Ran the prescribed saved-packet dry run before edits. It checked both Lean files on the server and exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. The wrapper reported `PREFLIGHT FAILED, nothing pushed`.

Compared both sandbox node records to current read-only main by JSON reads: the item differs only in `lean` and `stmt_deps`; the new definition is absent from main and retains the required `import_flags: ["unreachable"]`. This is return L's requested repair for immutable head `90b473dc935d`. No Lean or node content changed. Removing the flag undoes that repair, and modifying or bypassing the prescribed gate is forbidden. No direct Git mutations, live edits, or push were performed. Delivery remains blocked by the tool's refusal of required reachability metadata.

## Saved-packet repair verification 2026-10-22 09:59 UTC

Ran the required initial saved-packet dry run with the prescribed, unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server, refreshed its delivery bookkeeping, staged the packet, and exited 1 with exactly one preflight reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

It reported `PREFLIGHT FAILED, nothing pushed`. Read both retained Lean modules and compared both sandbox node records with current read-only main by JSON reads: the definition remains absent from main; the item differs only in `lean` and `stmt_deps`, and cites the new definition. Its `import_flags: ["unreachable"]` already implements return L for immutable head `90b473dc935d`. Removing this field would undo that repair. No Lean or node content was changed, no direct Git command or live edit was made, and no push was attempted. The prescribed gate must accept or apply the required reachability metadata; modifying or bypassing it is expressly forbidden.

## Saved-packet repair verification 2026-10-22 10:01 UTC

The required initial saved-packet `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push` checked both Lean files on the server and exited 1 with one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`. Read both retained Lean modules and compared the sandbox nodes with current read-only main by JSON reads: the definition remains absent from main; the item differs only in `lean` and `stmt_deps`. The definition retains `import_flags: ["unreachable"]`, as required by return L. Removing it would undo that repair; modifying or bypassing the prescribed gate is forbidden. No Lean or node content changed and no push was attempted.

## Saved-packet repair verification 2026-10-22 10:04 UTC

Ran the prescribed initial saved-packet `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server, staged the packet, and exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`.

Read both retained Lean modules and compared the node records with current read-only main by JSON reads: the item differs only in `lean` and `stmt_deps`; the new definition remains absent from main and retains `import_flags: ["unreachable"]`. The item cites that definition. The retained field implements return L for immutable head `90b473dc935d`; removing it undoes the repair. No Lean or node content changed, and no direct Git commands, live edits, launcher modifications or push were performed. The prescribed gate must accept or apply this required reachability metadata; bypassing or modifying it is forbidden by the launcher instructions.

## Saved-packet repair verification 2026-10-22 10:06 UTC

Ran the required initial saved-packet dry run with the prescribed unmodified
`deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
It checked both Lean files on the server and exited 1 with exactly one reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

The wrapper reported `PREFLIGHT FAILED, nothing pushed`. Compared both sandbox
node records to current read-only main by JSON reads: the new definition remains
absent from main; the item's only changed fields are `lean` and `stmt_deps`, and
it cites the definition. The definition retains `import_flags: ["unreachable"]`,
implementing return L for immutable head `90b473dc935d`. Removing the flag would
undo the requested repair. No Lean or node content was changed; no direct Git
commands, live edits, launcher modifications or push were performed. The
prescribed gate must accept or apply this required reachability metadata.

## Saved-packet repair verification 2026-10-22 10:07 UTC

Ran the required initial saved-packet dry run with the prescribed unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server and exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`.

Read both retained Lean modules and compared the sandbox nodes against current read-only main by JSON reads: the item differs only in `lean` and `stmt_deps`; the new definition remains absent from main. The item cites that definition, whose `import_flags: ["unreachable"]` implements return L for immutable head `90b473dc935d`. Removing the flag would undo the repair, and modifying or bypassing the gate is forbidden. No Lean or node content changed; no direct Git commands, live edits, launcher modifications or push were performed. The prescribed gate must accept or apply this required reachability metadata.

## Saved-packet repair verification 2026-10-22 10:11 UTC

Ran the prescribed initial saved-packet dry run before edits. It exited 1 with exactly one stage-2 preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. The wrapper reported `PREFLIGHT FAILED, nothing pushed`.

Read both retained Lean modules and compared the sandbox nodes with current read-only main by JSON reads: the new definition is still absent; the item differs only in `lean` and `stmt_deps`. The definition retains `import_flags: ["unreachable"]`, implementing return L at immutable head `90b473dc935d`. Removing it would undo the required repair. No Lean or node content changed, and no direct Git command, live edit, launcher modification, gate bypass or push was performed. The prescribed gate must accept or apply the required reachability metadata.

## Saved-packet repair verification 2026-10-22 10:13 UTC

Ran the required initial saved-packet dry run with the prescribed unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server and exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer’s fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`.

Compared the sandbox nodes with current read-only main using JSON reads: the item differs only in `lean` and `stmt_deps`; the new definition remains absent from main and retains the required `import_flags: ["unreachable"]`. The flag implements return L for immutable head `90b473dc935d`; removing it would undo the repair. No Lean or node content changed, and no direct Git command, live edit, launcher modification, gate bypass or push was performed. The prescribed gate must accept or apply this required reachability metadata.

## Saved-packet repair verification 2026-10-22 10:14 UTC

Ran the required initial saved-packet dry run using the unmodified prescribed deliver2.py with --no-push. It checked both Lean files on the server and exited 1: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`.

Read both retained Lean modules and compared both sandbox node records to current read-only main by JSON reads: the new definition remains absent; the item differs only in `lean` and `stmt_deps` and cites it. The definition retains `import_flags: ["unreachable"]`, implementing return L for immutable head `90b473dc935d`. Removing it undoes the required repair. No Lean or node content changed, no direct Git commands or live edits were made, and no push was attempted. The prescribed gate must accept or apply this metadata; modifying or bypassing the gate is forbidden by the launcher instructions.

## Saved-packet repair verification 2026-10-22 10:16 UTC

Ran the required initial saved-packet dry run with the prescribed unmodified
`deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
It checked both Lean files on the server, staged the packet, and exited 1 with
exactly one preflight reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

The wrapper reported `PREFLIGHT FAILED, nothing pushed`. Read both retained Lean
modules and compared both sandbox node records with current read-only main using
JSON reads: the new definition remains absent; the item differs only in `lean`
and `stmt_deps` and cites the definition. The definition retains
`import_flags: ["unreachable"]`, implementing return L at immutable head
`90b473dc935d`. Removing it would undo that repair. No Lean or node content
changed, no direct Git command or live edit was made, and no push was attempted.
The prescribed gate must accept or apply this required reachability metadata;
modifying or bypassing the launcher gate is expressly forbidden.

## Saved-packet repair verification 2026-10-22 10:19 UTC

The required initial saved-packet dry run checked both Lean files on the server, then exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`. Read both retained modules and compared sandbox node records to current read-only main using JSON reads: the new definition remains absent; the item differs only in `lean` and `stmt_deps` and cites it. The definition retains `import_flags: ["unreachable"]`, implementing return L at immutable head `90b473dc935d`. Removing it would undo the required repair. No Lean or node content changed, and no direct Git commands, live edits, launcher modifications or push were performed. The prescribed gate must accept or apply this required reachability metadata; modifying or bypassing it is forbidden.

## Saved-packet repair verification 2026-10-22 10:24 UTC

Ran the prescribed initial saved-packet dry run with the unmodified
`deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
It checked both Lean files on the server, refreshed its delivery bookkeeping,
and exited 1 with exactly one preflight reason:
`(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`.
The wrapper reported `PREFLIGHT FAILED, nothing pushed`.

Read both retained Lean modules and compared both sandbox node records against
current read-only main by JSON reads: the new definition remains absent from main;
the item differs only in `lean` and `stmt_deps` and cites the definition.
The definition retains `import_flags: ["unreachable"]`, implementing return L
for immutable head `90b473dc935d`. Removing it would undo the requested repair.
No Lean or node content changed, and no direct Git mutation, live edit, launcher
modification, gate bypass or push was performed. Delivery requires the prescribed
gate to accept or apply this required reachability metadata.

## Saved-packet repair verification 2026-10-22 10:26 UTC

Ran the required initial saved-packet dry run using the prescribed unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server and exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`.

Read both retained Lean modules and compared both sandbox node records to current read-only main using JSON reads: the new definition remains absent; the item differs only in `lean` and `stmt_deps` and cites the definition. The retained `import_flags: ["unreachable"]` implements return L at immutable head `90b473dc935d`. Removing it undoes the requested repair. No Lean or node content changed; no direct Git commands, live edits, launcher modifications, gate bypass or push were performed. The prescribed gate must accept or apply the required reachability metadata.

## Saved-packet repair verification 2026-10-22 10:28 UTC

Ran the required initial saved-packet dry run using the prescribed unmodified
`deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
It checked both Lean files on the server and exited 1 with exactly one reason:
`(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`.
The wrapper reported `PREFLIGHT FAILED, nothing pushed`.

Read both retained Lean modules and compared the sandbox node records with current
read-only main using JSON reads: the new definition remains absent from main;
the item differs only in `lean` and `stmt_deps` and cites the new definition.
Its retained `import_flags: ["unreachable"]` implements return L at immutable
head `90b473dc935d`. Removing that flag undoes the required repair. No Lean or
node content changed, and no direct Git command, live edit, launcher modification,
gate bypass or push was performed. The prescribed gate must accept or apply the
required reachability metadata.

## Saved-packet repair verification 2026-10-22 10:32 UTC

Ran the prescribed initial saved-packet dry run with the unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server and exited 1 with one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`.

Read both retained Lean modules and compared the sandbox nodes to current read-only main using JSON reads: the new definition remains absent; the item differs only in `lean` and `stmt_deps` and cites the definition. The retained `import_flags: ["unreachable"]` implements return L at immutable head `90b473dc935d`. Removing it would undo that repair. No Lean or node content changed, no direct Git commands or live edits were made, and no push was attempted. The prescribed gate must accept or apply this metadata; modifying or bypassing it is expressly forbidden by the launcher instructions.

## Saved-packet repair verification 2026-10-22 10:35 UTC

Inspected the saved report and ran the prescribed unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push` before edits. The wrapper checked both Lean files on the server, staged the packet, and exited 1 with `PREFLIGHT FAILED, nothing pushed`. Its sole preflight reason was `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It also reported that delivery base `8ac8ee967` had moved behind sheaf-dag.

Read both retained Lean modules and compared the node JSON with current read-only main: the item differs only in `lean` and `stmt_deps`; the new definition remains absent from main and retains `import_flags: ["unreachable"]`, the explicit repair required by return L at immutable head `90b473dc935d`. Removing that field undoes the repair. No Lean or node changes, direct Git commands, live edits, launcher-tool modifications, or push were performed. The prescribed gate must accept or apply the required reachability metadata before delivery can proceed.

## Saved-packet repair verification 2026-10-22 10:38 UTC

Inspected the saved report and both retained Lean modules. The required initial dry run using the unmodified prescribed `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push` checked both Lean files on the server and exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`. Compared node JSON against current read-only main: the item differs only in `lean` and `stmt_deps`; the new definition remains absent and retains `import_flags: ["unreachable"]`, implementing return L at immutable head `90b473dc935d`. No Lean or node content changed. Removing the flag would undo the required reachability repair; modifying or bypassing the prescribed gate is forbidden. No direct Git command, live edit, launcher modification or push was performed. The gate must accept or apply the required metadata.

## Saved-packet repair verification 2026-10-22 10:46 UTC

Inspected the saved packet and ran the required initial unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server and exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`, with delivery base `aeb6b9d86`.

Compared sandbox nodes with current read-only main by JSON reads: the definition remains absent; the item differs only in `lean` and `stmt_deps` and cites it. The retained `import_flags: ["unreachable"]` implements return L at immutable head `90b473dc935d`. Removing it would undo the reachability repair; modifying or bypassing the prescribed gate is forbidden. No Lean or node content changed, no direct Git commands or live edits were made, and no push was attempted. The prescribed gate must accept or apply this required metadata.

## Saved-packet repair verification 2026-10-22 10:49 UTC

Inspected the saved report and both Lean modules, then ran the prescribed unmodified initial saved-packet `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server and exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`.

Compared sandbox node JSON with current read-only main: the definition remains absent; the item differs only in `lean` and `stmt_deps`. The retained `import_flags: ["unreachable"]` implements return L at immutable head `90b473dc935d`. Removing it would undo the required repair. No Lean or node content changed, and no direct Git command, live edit, launcher modification, gate bypass or push was performed. The prescribed gate must accept or apply this required metadata.

## Saved-packet repair verification 2026-10-22 10:52 UTC

Inspected the saved report, both Lean modules and both node records, then ran the prescribed unmodified initial `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`. Compared the sandbox node records with current read-only main by JSON reads: the definition remains absent; the item differs only in `lean` and `stmt_deps`. Retained the required `import_flags: ["unreachable"]` implementing return L. Removing it undoes the repair; changing or bypassing the delivery gate is forbidden. No Lean or node content changed, no direct Git commands or live edits were made, and no push was attempted. The prescribed gate must accept or apply this metadata.

## Saved-packet repair verification 2026-10-22 10:54 UTC

Inspected the saved report, both retained Lean modules and both node records, then ran the prescribed unmodified initial `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. The wrapper checked both Lean files on the server and exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`. JSON comparison against current read-only main confirms that the definition remains absent and the item differs only in `lean` and `stmt_deps`. The retained `import_flags: ["unreachable"]` implements return L at immutable head `90b473dc935d`. Removing it would undo the required repair; modifying or bypassing the prescribed gate is forbidden. No Lean or node content changed, no direct Git command or live edit was made, and no push was attempted. Delivery requires the prescribed gate to accept or apply this required reachability metadata.

## Saved-packet repair verification 2026-10-22 11:00 UTC

Ran the prescribed initial saved-packet dry run with the unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server, completed its shared fetch and staging, then exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`.

Read both retained modules and compared sandbox node JSON with current read-only main: the definition remains absent; the item differs only in `lean` and `stmt_deps`. The retained `import_flags: ["unreachable"]` implements return L at immutable head `90b473dc935d`. Removing it would undo that repair. No Lean or node content changed; no direct Git command, live edit, launcher modification, gate bypass or push was performed. The prescribed gate must accept or apply this required reachability metadata.

## Saved-packet repair verification 2026-10-22 11:08 UTC

Ran the prescribed saved-packet dry run before edits. The unmodified delivery
wrapper checked both Lean files on the server, refreshed its own bookkeeping,
and exited 1 with one preflight reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

It reported `PREFLIGHT FAILED, nothing pushed`. Read both retained Lean modules
and compared both sandbox node records with current main using JSON reads: the
new definition is absent from main, the item differs only in `lean` and
`stmt_deps`, and the definition retains `import_flags: ["unreachable"]`, the
repair required by return L for immutable head `90b473dc935d`. Removing that
flag would undo the requested repair; modifying or bypassing the prescribed
gate is expressly forbidden. Retained both nodes and both Lean modules without
changes. No direct Git command, live edit, or push was performed. The delivery
gate must permit or apply the required reachability metadata.

## Saved-packet repair verification 2026-10-22 11:16 UTC

Inspected the retained report and ran the prescribed initial saved-packet dry run
using the unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
The wrapper checked both Lean files on the server, staged the packet, and exited 1
with exactly one preflight reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

It reported `PREFLIGHT FAILED, nothing pushed` and delivery base `6f3dafa6d`.
Read both retained Lean modules and compared sandbox node JSON with current
read-only main: the definition remains absent; the item differs only in `lean`
and `stmt_deps` and cites the definition. The definition retains
`import_flags: ["unreachable"]`, implementing return L at immutable head
`90b473dc935d`. Removing the flag would undo the required reachability repair.
No Lean or node content changed; no direct Git command, live edit, launcher
modification, gate bypass or push was performed. The prescribed gate must accept
or apply this required metadata before delivery can proceed.

## Saved-packet repair verification 2026-10-23 04:41 UTC

Inspected the retained report and ran the prescribed initial saved-packet dry run
using the unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
It checked both Lean files on the server and exited 1 with exactly one preflight reason:
`(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`.
It reported `PREFLIGHT FAILED, nothing pushed`. Read both retained Lean modules
and compared the sandbox node records with current read-only main using JSON reads:
the new definition remains absent; the item differs only in `lean` and `stmt_deps`.
The definition retains `import_flags: ["unreachable"]`, implementing return L
at immutable head `90b473dc935d`. Removing it would undo the required repair.
No Lean or node content changed; no direct Git command, live edit, launcher
modification, gate bypass or push was performed. The prescribed gate must accept
or apply the required reachability metadata before delivery can proceed.

## Saved-packet repair verification 2026-10-23 04:48 UTC

Ran the required initial unmodified `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`. It checked both Lean files on the server and exited 1 with exactly one preflight reason: `(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. It reported `PREFLIGHT FAILED, nothing pushed`. Read both retained modules and compared sandbox nodes with current read-only main using JSON reads: the definition remains absent; the item differs only in `lean` and `stmt_deps`, citing that definition. The retained `import_flags: ["unreachable"]` implements return L at immutable head `90b473dc935d`. Removing it would undo the required repair. No Lean or node content changed, no direct Git command or live edit was performed, and no gate modification, bypass or push was attempted. The prescribed gate must accept or apply the required metadata.

## Saved-packet repair verification 2026-10-23 04:54 UTC

Ran the required initial saved-packet dry run with the prescribed unmodified
`deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
Both Lean files passed server compilation, but stage-2 preflight exited 1 with
exactly one reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

The wrapper reported `PREFLIGHT FAILED, nothing pushed`. Read both Lean modules
and compared the sandbox nodes against current read-only main by JSON reads:
the item differs only in `lean` and `stmt_deps`; the new definition remains absent
from main and retains `import_flags: ["unreachable"]`, the repair required by
return L at immutable head `90b473dc935d`. Removing that field would undo the
returned repair. No Lean or node changes, direct Git commands, live edits,
launcher-tool modifications, or push were performed. The delivery gate must
accept or apply the required reachability metadata before delivery can succeed.

## Saved-packet repair verification 2026-10-23 05:13 UTC

Ran the required initial saved-packet dry run with the prescribed, unmodified
`deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
The wrapper checked both Lean files on the server and exited 1 at preflight
with exactly one reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

It reported `PREFLIGHT FAILED, nothing pushed`. Read both retained modules
and compared both sandbox node records to current main by JSON reads: the
item differs only in `lean` and `stmt_deps`; the new definition is absent
from main and retains `import_flags: ["unreachable"]`. The current delivery
wrapper therefore still treats this definition as new. Return L at immutable
head `90b473dc935d` requires this reachability repair; removing the flag would
undo it. Both Lean sources and both node records are retained unchanged.
No launcher script, project tool, live file, or Git state was directly modified,
and no push was attempted. The prescribed gate must accept this flag, or the
maintainer must register the definition with its reachability metadata before
a lean-only dependency delivery can pass.

## Saved-packet repair verification 2026-10-23 05:21 UTC

Ran the prescribed initial saved-packet dry run without changing its contents:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
Both Lean files were checked on the server. The wrapper exited 1 with one
preflight reason and reported `PREFLIGHT FAILED, nothing pushed`:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

Compared the retained node records with current read-only main using JSON reads:
the item's differing fields are lean, stmt_deps; the new definition remains
absent from main. The item cites the new definition, whose retained
`import_flags: ["unreachable"]` addresses return L at immutable head
`90b473dc935d`. Removing that flag would undo the required repair. The prescribed
gate still refuses this maintainer-owned field, and launcher instructions forbid
patching or bypassing the gate. Retained both Lean modules and both node records
unchanged; no direct Git commands, live writes, launcher modifications, or push
were performed. The gate must accept or apply the required reachability metadata.

## Saved-packet repair verification 2026-10-23 06:12 UTC

Ran the required initial saved-packet dry run with the unmodified prescribed
`deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`.
The wrapper checked both Lean files on the server, staged the packet, and
exited 1 with exactly one preflight reason:

```text
(b) new node def-sfb-space-morphism-properties: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

It reported `PREFLIGHT FAILED, nothing pushed`. Read both retained Lean modules
and compared sandbox node JSON with current read-only main: the new definition
remains absent; the item differs only in `lean` and `stmt_deps` and cites it.
The definition retains `import_flags: ["unreachable"]`, implementing return L
at immutable head `90b473dc935d`. Removing the flag would undo the required
repair. The brief expressly forbids modifying or bypassing a refusing gate.
Both Lean modules and both node records were retained unchanged; no direct
Git commands, live edits, launcher modifications or push were performed.
Delivery requires the prescribed gate to accept or apply this reachability
metadata.

## Second reading by Q104

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
