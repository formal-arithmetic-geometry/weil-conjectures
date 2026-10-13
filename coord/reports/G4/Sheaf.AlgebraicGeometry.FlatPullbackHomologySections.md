## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_openMap_sections`
to the raw cycle-class identity for the two pushforward resolution complexes. The main module
proves the adjunction transport through the derived-image isomorphisms, proves a generic
formula for resolutionSectionClass, identifies the source and target class maps, and cancels
the pinned resolution-section isomorphisms before evaluating at xi. Its original
signature, including both flatness hypotheses and arbitrary t, stays unchanged.

The proof-settings change record is
`coord/changes/flat-pullback-homology-proof-settings.md`. It documents only file-local
attributes and elaboration settings; no existing public signature or definition changes.

Added the proof-only import `Sheaf.AlgebraicGeometry.FlatPullbackResolutionRawMateSections`.
The new statement has no open-choice record D, no open cohomology element xi, no restricted
resolution, and no derived-image or resolution-section isomorphism. It isolates the raw-complex
cycle calculation; the main theorem combines that calculation with the transport steps.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_openMap_sections`
(node `lem-weil-pbc-flat-pullback-homology-sections`).

Added one named hole:
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolution_rawMate_sections`
(node `lem-weil-pbc-flat-pullback-resolution-raw-mate-sections`). Its proof is exactly `by sorry`.
Its docstring and node give the unit-on-cycles, exact pullback, theta-naturality, and complex
adjunction argument. This is a decomposition: one upper hole closed and one strictly smaller
lower hole added. Every private helper theorem in the main module is proved, and its private
raw class definition is a real construction.

The raw statement covers degree zero and empty opens; it does not assert that theta is
invertible or that global sections preserve arbitrary sheaf-complex homology.

## No longer needed

No imports or modules are pruned. The original public import stays.
The old direct proof dependency
`lem-weil-pbc-flat-module-pullback-exact-pushforward-injective` is replaced in the
parent node by `lem-weil-pbc-flat-pullback-resolution-raw-mate-sections`; exactness
remains needed transitively in that raw lemma and in the comparison isomorphism.
The adjunction, open-choice theta definition, construction of q and c, and open-map
definition stay as direct dependencies. The blueprint unit's statement and its
realized proof steps remain.

## Where the brief, the DAG or earlier work was wrong

The static preflight treats added file-local irreducibility attributes as an interface
change and requires a change record; the scoped settings do not propagate to importers.

The plan's raw cycle-class calculation is not a directly usable theorem of the library.
The raw calculation remains the outstanding mathematical step. The reduction separates it
from the resolution transports, which the main module proves. During repair, repeated
unfolding of the target class and open-map constructions caused expensive definitional
comparisons; a proved generic class-map identity and controlled unfolding address those
comparisons without changing any definition or splitting a file to evade the time limit.
The local cache initially lacked the newly landed FlatBaseChangeResolutionOpenMap; generic
work continued until its compiled module became available.
The cited Stacks source files are absent from this read-only checkout; Tags
[01E4](https://stacks.math.columbia.edu/tag/01E4) and
[02N7](https://stacks.math.columbia.edu/tag/02N7) were read online.

## New nodes

`lem-weil-pbc-flat-pullback-resolution-raw-mate-sections`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-pullback-resolution-raw-mate-sections.json`,
records the raw homology-mate identity, its proof in words, searches, and exact Lean signature.
Its module is `Sheaf.AlgebraicGeometry.FlatPullbackResolutionRawMateSections`.
No existing declaration interface changes and no forced adaptations are needed.
The conservative preflight requirement is documented in
`coord/changes/flat-pullback-homology-proof-settings.md`.

## Second reading by G4

1. PASS: Compared the main module with the read-only repository using diff and
   checked the existing public theorem signature byte for byte. Both flatness
   hypotheses, arbitrary t, D, xi, and the conclusion are unchanged. No existing
   definition body or visibility changes. The new helpers are private; the
   proof-settings record covers the local attributes and elaboration options.
2. PASS: Compiled both delivered modules in import order with lcompile.py --all,
   with no errors or warnings. The main module has no sorry; the new module has
   exactly the one reported public named theorem whose proof is by sorry.
   Neither module has a forbidden declaration or a hollow definition. The
   rawSectionClass helper explicitly composes the exact evaluation comparison
   with theta; it chooses no witness. Axiom inspection is recorded below.
3. PASS: Read the raw lemma against its Lean signature, docstring, node, and
   definitions of q, c, theta and beta. Exact pullback and unit naturality send
   cycles to cycles and commute with the homology quotient; theta sends those
   cycles to their sheaf classes. Composing with c gives q by the complex
   adjunction. This argument does not require theta to be invertible, or any
   augmentation condition on t. Checked p=0 (zero incoming differential),
   empty V (zero section groups), zero t (both induced maps zero), and the
   identity base morphism (the same cycle naturality square). The lemma omits
   the restricted resolutions, D, xi, and all resolution and derived-image
   transports, so it is strictly a part of the argument rather than a renamed
   parent statement. It has its named hole, complete proof in words, and node.
   Repeated LeanFinder, Loogle, and rg searches with cycle/quotient/unit queries;
   recorded results on the new node. Read ShortComplexSectionComparison,
   HigherDirectImageResolutionNaturality and FlatScalarExtensionHomologyAdjunct.
   Their generic/private ingredients do not give this scheme section formula.
   Closing the raw lemma requires the flat-unit comparison in addition to
   theta's cycle formula; it is not a few-minute application of those results.
   Read Stacks Tags [01E4](https://stacks.math.columbia.edu/tag/01E4) and
   [02N7](https://stacks.math.columbia.edu/tag/02N7) online for the source route.
4. PASS: The main proof really proves adjunction transport, the generic
   resolutionSectionClass formula, both class-map identifications, and the
   source and target cancellations before applying the morphism equality to xi.
   The public OpenMap import is needed by the signature; the new RawMate import
   is proof-only. The raw module's public import supplies its statement's
   constructions and exactness instances. No shorter complete library route
   was found. Corrected No longer needed to name the old exactness dependency
   removed from the parent's direct proof_deps but retained transitively in the
   raw lemma. No import or module is pruned. Read sk-thm-p1's realized statement
   and proof steps; no unit realization or route is bypassed or changed.
5. PASS: Both nodes' proof_deps equal the union of their proof steps' uses.
   The parent's three steps match the raw calculation, adjunction transport,
   and class-map cancellations in Lean. The new node's Lean statement matches
   the module byte for byte and has all required source, proof, search,
   provenance, creation, blueprint, chapter, unit, and Lean fields. Existing
   node edits are confined to proof, proof_deps, and proof_origin.

Second reading changed only the pruning/dependency explanation in this report,
added the independent search records on the new node, and added this review.
No Lean code, existing signature, definition, or unit record needed repair.

Axiom check: the scratch import module compiled, and #print axioms for both
flatBaseChangeResolutionBeta_openMap_sections and
flatBaseChangeResolution_rawMate_sections printed exactly propext, sorryAx,
Classical.choice, and Quot.sound. The expected sorryAx remains because the raw
lemma is still open. The delivery's probe checks every delivered declaration.
