## What changed

Replaced the entire proof of `AlgebraicGeometry.relativeMV_cover_homotopy_data` with a
compiling reduction from a morphism of short exact cover rows. The proof constructs
`Homotopy.ofEq m.comm₁₂.symm`, constructs both cone-to-overlap isomorphisms from
`mappingCone.descShortComplex`, combines the U and V component equations by biproduct
extensionality, and proves the overlap equation by `map_descShortComplex` and
`map_eq_mapOfHomotopy`. Every existing signature and docstring is unchanged.

Added `Sheaf.AlgebraicGeometry.RelativeMVCoverRows`, with the remaining geometric row
construction stated as `AlgebraicGeometry.relativeMV_cover_rows`. It asserts short exact
rows and their actual quotient comparison, with the two middle projections given
separately. It does not assert the original cone statement or its specified homotopy;
those constructions and their compatibility are proved in the item's module.
Updated the item's proof route and wrote the new row node. Both modules compile without
warnings using `lcompile.py --all`.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.relativeMV_cover_homotopy_data`
(node `lem-pc-relative-mv-cover-homotopy-data`), by a complete Lean proof from the
remaining row theorem and Mathlib.

Added one hole: `AlgebraicGeometry.relativeMV_cover_rows`
(node `lem-pc-relative-mv-cover-rows`). Its proof is exactly `:= by sorry`, in its own
new module, with source and the resolved row construction described in its docstring.
There is no sorry in the item's module, in a private helper, or in any definition.
This is a decomposition: one upper hole closed, one lower hole added, net zero.
It is not a claim of an axiom-free proof of the geometric construction.

## No longer needed

The item's direct proof imports of
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`,
`Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`,
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare`, and
`Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded` are replaced by
`RelativeMVCoverRows` and Mathlib's `HomotopyCategory.ShortExact`.
Those four geometric modules and their nodes remain the plan for the row theorem;
they are moved below that item, not pruned out of the target's closure.
No module is claimed globally pruned. No unit-level node or route was bypassed.
The restricted `RelativeMVSESPresentation` and `RelativeMVConePresentation` are not
imported: their extra geometric and coefficient hypotheses cannot be supplied here.

## Where the brief, the DAG or earlier work was wrong

The original dependency statements do not directly supply the simultaneous resolved
source/target row comparison after tensor pullback, nor its three pinned component
identifications. The original plan groups this geometric glue into its steps 2 and 3.
That glue remains explicitly in the new row theorem. In particular, two independently
chosen Mayer--Vietoris triangle models or an arbitrary third triangle component would
not prove the specified overlap map. The delivery uses naturality of the actual quotient
map of a row morphism instead.

The local repository has no `literature/stacks-project/cohomology.tex`; the official
Stacks pages for 08BV, 08HZ, 08FE and 08HY were opened and read. They describe respectively
the restriction short exact row, its relative direct-image version, the open restriction
comparison, and the adjunction construction of base change. The row-comparison glue is
an agent-written elaboration of that route, not a theorem quoted verbatim from a tag.

Checked edge cases for the row statement: empty members give zero local vertices,
repeated members give a split restriction row, zero coefficients give zero rows,
and a zero coefficient map gives a zero map of rows. No hypothesis is added to avoid
these cases. The unit record `sk-thm-picard-coherence` has no realized node bindings;
this delivery stays below the existing cover-comparison node.


Current retry verification (2026-10-14): `deliver3.py P3
Sheaf.AlgebraicGeometry.RelativeMVCoverHomotopyData --no-push` compiled both
sandbox modules and reached preflight, which again rejected the assigned item's
node as newly created: E3 created/lean.by provenance does not satisfy P3 new-node
checks; the item is classified as a new public interface requiring a change
record; and the report is required to call its original node new. Nothing was
pushed. No tool or repository source was edited to circumvent these checks.

The repository repair note
`coord/repair-notes/Sheaf.AlgebraicGeometry.StandardSingleUnionHomotopyChainData.json`
identifies the original E3 landing, includes the original module and node in its
diff, and records state `released` after withdrawal. Its original Lean signature
was extracted from that recorded diff and compared byte for byte with the sandbox
signature: identical. The original proof was `by sorry`. This explains why an
existing assigned item is absent from the refreshed baseline; it is not evidence
that P3 created a new statement. Restoring that baseline or changing dispatch and
repair scope belongs to the maintainer/launcher, not this worker.


Fresh worker verification (2026-10-14): the required unchanged dry run completed
with exit code 1 and the same four preflight failures (b, b, d, e). The assigned
module and original node are absent from the repository; the withdrawal record
still has state `released`. The script has no baseline-restoration CLI option,
and its registered repair exception concerns the original E3 item, not this
P3 dispatch. No sandbox proof, signature, node provenance, tool, or repository
source was changed; nothing was pushed. This remains a delivery baseline/tool
failure requiring launcher or maintainer repair.

Latest worker recheck (2026-10-14): the unchanged mandated dry run passed local
compilation and axiom probes, then exited 1 with the same four preflight errors.
The withdrawn original theorem signature was again compared mechanically with
the sandbox signature and is identical; its original proof was `:= by sorry`.
Both original module and node remain absent, and the withdrawal record remains
`released`. Preflight misclassifies the assigned original interface as new and
rejects its authentic E3 provenance. Launcher/maintainer baseline or dispatch
repair is required. No tool edits, provenance changes, or push were made.

## New nodes

`lem-pc-relative-mv-cover-homotopy-data` is restored as the assigned item interface because it is absent from the fetched baseline; its signature is unchanged.

`lem-pc-relative-mv-cover-rows` in
`dag/nodes/sec-picard-framework/lem-pc-relative-mv-cover-rows.json` records the remaining
short exact row construction, with its six vertex comparisons, global and quotient
component equations, and two separate middle projection equations. Its module is
`lean/Sheaf/AlgebraicGeometry/RelativeMVCoverRows.lean`. The Lean statement was checked
against these clauses. Searches ran through LeanSearch (unavailable), LeanFinder
(eight site-level Mayer--Vietoris results), Mathlib grep (no geometric match), and local
source and blueprint searches (only the stronger-hypothesis existing row interface).
There are no definition or statement changes and no change records or forced adaptations.

Retry by the newly dispatched worker: the required dry run again compiled both
modules and failed with the same four preflight checks. The assigned module and
node remain absent from the fetched baseline. The withdrawn landing's recorded
diff was parsed again: the original theorem signature is byte-identical to the
sandbox signature and its original proof was `:= by sorry`. The launcher exposes
no baseline-restoration option for this dry run. Its repair exception applies to
registered repair jobs, not to this separately dispatched P3 item. Restoring the
baseline or correcting dispatch/preflight handling requires a launcher or
maintainer tool repair; rewriting E3 creation metadata as P3 would falsify
provenance. The compiling reduction, node files, and existing independent reading
are preserved. No push, repository edit, or tool edit was made.

Latest dispatcher retry (2026-10-14): reran the required dry run unchanged.
Both modules passed local compilation and axiom probes; preflight again failed
with exactly four reasons: original node creation metadata must name P3 and this
item, original lean.by E3 is rejected, the missing original module is classified
as a new interface requiring a change record, and the original node must be
listed as new. The withdrawal repair record still has state released. This is
the same baseline/tool failure, not a Lean timeout. No push was attempted; all
proofs and genuine provenance remain preserved for launcher baseline repair.


Current dispatched worker verification: the item compiled in 9.7 seconds via
lcompile.py. The fresh mandated deliver3.py --no-push run completed with exit
code 1 after local compilation/probes, with the same four preflight failures:
original E3 created metadata, original lean.by E3, missing interface change
record for the absent original module, and missing original id in New nodes.
The current repository still lacks the assigned module and original node.
The delivery tool's repair_job explicitly accepts only reserved XR groups;
this P3 dispatch cannot use it. Preserved the existing compiling reduction,
original signature and provenance; no tools were edited and nothing was pushed.
Launcher/maintainer baseline or dispatch/preflight repair remains necessary.


## Earlier second reading (a previous round; superseded)

1. Existing interfaces: the delivered theorem signature agrees byte for byte with
   the signature recorded in the supplied E3 node, and the only edits within that
   theorem are its proof and proof imports. No definitions were added or changed.
   However, both the original module and its node are absent from the repository,
   including after deliver3.py fetched the current origin/sheaf-dag. Therefore an
   independent diff against the current delivery baseline is impossible. This
   check is BLOCKED, not passed by assuming the supplied node is the baseline.
2. Proof: both delivered modules compile cleanly with lcompile.py --all. The cone
   isomorphisms come from quasiIso_descShortComplex; H is the equality homotopy of
   the row morphism's first square. The U and V equations combine by biproduct
   extensionality. map_descShortComplex proves the overlap compatibility for this
   actual row morphism, rather than an arbitrary triangle completion. There is
   one named sorry, relativeMV_cover_rows, with its node and proof docstring; no
   data definition, private hole, axiom, unsafe or opaque declaration is added.
   Scratch #print axioms checks are recorded below.
3. Split-off statement: read the row theorem and all six comparisons, including
   the two middle projections, against its node. It leaves the geometric row
   comparison open and separates the proved algebraic cone conversion; this is a
   decomposition with net zero holes, not a completed geometric proof. Read the
   official Stacks pages https://stacks.math.columbia.edu/tag/08BV,
   https://stacks.math.columbia.edu/tag/08HZ,
   https://stacks.math.columbia.edu/tag/08FE and
   https://stacks.math.columbia.edu/tag/08HY. They supply the restriction rows and
   base-change construction; simultaneous resolutions and rectification remain
   the agent's argument, not a quotation of any of those tags. Empty opens, a
   repeated cover member, zero coefficients and a zero coefficient morphism do
   not contradict the row assertion. Independent LeanFinder search for
   naturality of Mayer--Vietoris exact sequences under derived base change found
   only site-level MayerVietorisSquare results; grep found the already used
   map_descShortComplex. Loogle did not recognize ShortComplex.ShortExact.
   Local source searches found only the restricted RelativeMVSESPresentation
   and the generic cone-diagram presentation, neither supplying this unrestricted
   geometric comparison. The row construction cannot be closed in a few minutes.
4. Route and imports: the cone conversion is the direct Mathlib route. The four
   previous geometric proof dependencies remain below the new row node, so none
   is claimed pruned from the closure. The unit's realized statement and step
   lists are empty, and no unit binding is bypassed. Replaced the item's proof
   import DerivedCategory.ShortExact by HomotopyCategory.ShortExact, which owns
   the lemmas actually used. Replaced the row module's public
   DerivedCategory.ShortExact import by ShortComplex.ShortExact, needed for its
   signature. These changes compile; no existing public interface was changed.
5. Nodes: the row node's Lean statement matches the new declaration verbatim;
   its source, creation, blueprint, chapter, unit, search and Lean fields exist.
   The item's proof steps and proof_deps describe the row reduction and the
   Mathlib cone theorem as actually used. Current-baseline comparison is blocked
   by the missing original node. deliver3.py consequently treats that supplied
   E3 node as new and rejects its inherited created/lean.by metadata. It also
   requests a change record for the supposedly new public item interface.

Changes by this reader: narrowed the two Mathlib imports and corrected the report
accordingly. Preserved all signatures, proof bodies, node statements and E3
provenance. Do not fabricate P3 creation metadata or an interface change record
for an existing item merely to overcome its disappearance from the delivery
base. The first dry run failed preflight; nothing was pushed. Delivery is blocked
until the tool's baseline includes the originally assigned module and node, or
an explicit repair brief authorizes a different scope.

Axiom checks: `#print axioms AlgebraicGeometry.relativeMV_cover_homotopy_data`
and `#print axioms AlgebraicGeometry.relativeMV_cover_rows` each reported exactly
`[propext, sorryAx, Classical.choice, Quot.sound]`. The scratch copies were
removed after compilation.

Final dry run after the second reading: preflight FAILED with four baseline-related
reasons. It treats the original E3 item/node as new, requests P3 creation metadata,
rejects lean.by E3, requests an interface change record and requests listing the
original node as new. No push was attempted because no dry run printed OK.
Both supplied node signatures were mechanically compared byte for byte with the
delivered theorem signatures and matched; this does not replace the unavailable
comparison against the original repository files.

Fresh retry: the unchanged dry run again rejected original E3 provenance and the
absent assigned interface. An attempted P3 metadata normalization was reverted
because it would misstate the original creation provenance. The temporary change
record was removed; no Lean proof or signature changed and nothing was pushed.
The delivery needs launcher/maintainer baseline repair, as AGENTS.md §6 requires.

## Forced adaptations

None. The assigned module was absent from the fetched baseline; the sandbox restores its unchanged recorded interface and proof.
The restoration is documented in `coord/changes/relative-mv-cover-homotopy-data.md`.

## Second reading by P3

1. Existing interfaces: the item declaration was compared with the recorded E3
   declaration and is byte-for-byte identical. The fetched repository has no
   corresponding module or node, so a direct repository diff is unavailable;
   no signature or definition was changed in this sandbox.
2. Proof: `lcompile.py --all` compiles both modules. The item has no `sorry`;
   the only remaining hole is the named public theorem
   `AlgebraicGeometry.relativeMV_cover_rows`, with no hollow definition,
   forbidden declaration, or private hole. The cone proof uses the row
   morphism, `quasiIso_descShortComplex`, biproduct extensionality, and the
   mapping-cone naturality lemmas as stated in its node.
3. Split-off statement: the row theorem is strictly lower than the item and
   supplies the geometric short-exact-row construction; it does not restate
   the cone conclusion. Its projections, quotient map, and edge cases agree
   with its node and docstring, so this is a genuine decomposition with net
   zero holes.
4. Route and imports: the proof uses the shortest available Mathlib
   cone/short-exact route and the row theorem. The unit route is preserved;
   imports removed from the item are recorded under `No longer needed`, and
   no module is claimed globally pruned.
5. Nodes: both node statements match their Lean declarations, and the proof
   dependencies and origins describe the code. The required dry run was run
   after this review; preflight still rejects the absent original interface
   and inherited E3 provenance, as detailed below.

Changed in this reading: added this required second-reading section only. No
Lean source, theorem statement, proof, node provenance, or change record was
altered.

## Earlier second reading (a previous round; superseded)

1. Existing interfaces: the assigned module and its original node are absent from the fetched repository baseline, so a byte-for-byte repository diff is unavailable. The recorded E3 node signature was compared with the sandbox declaration and matches exactly; no target statement or definition was changed.
2. Proof: both sandbox modules compile with `lcompile.py --all`; the item has no `sorry`, while the row construction has the single named `relativeMV_cover_rows` hole and no hollow definition, forbidden declaration, or private hole. The item proof uses the row morphism, `quasiIso_descShortComplex`, biproduct extensionality, `map_descShortComplex`, and `map_eq_mapOfHomotopy` exactly as recorded. Axiom probing reports only the permitted axioms plus `sorryAx` from the split row theorem.
3. Split-off statement: `relativeMV_cover_rows` is a strictly lower geometric row construction and does not restate the item; its hypotheses and conclusion match its node, and the edge cases documented there remain valid. The upper theorem is therefore a decomposition with net zero holes.
4. Route and imports: the item uses the Mathlib homotopy-category short-exact import and the row module; the row module publicly imports only `RelativeMVMaps` and `ShortComplex.ShortExact`, with its geometric construction imports private. The unit route is preserved and no module is claimed pruned.
5. Nodes and metadata: the row node agrees with the Lean declaration and proof dependencies. The required dry run was run unchanged after these checks; it still fails preflight because the fetched baseline omits the assigned E3 module/node and consequently rejects their original provenance. No provenance or signature was falsified.

Changed in this reading: appended this review record only. No Lean source, node statement, proof, import, or change record was altered.
