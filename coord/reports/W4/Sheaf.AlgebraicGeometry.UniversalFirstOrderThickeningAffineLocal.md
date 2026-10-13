## What changed

Proved `AlgebraicGeometry.FormallyUnramified.exists_affine_local_universalFirstOrderThickening`
without changing its signature or its public imports. The proof constructs an affine source
cover over affine base charts by pullback and refinement, applies the existing ring existence
and spectrum universality theorems, transports through affine-spectrum isomorphisms, enlarges
the open base, and applies a cover-gluing theorem. The added proof imports are
`Sheaf.AlgebraicGeometry.UniversalThickeningAffineCase`,
`Sheaf.RingTheory.UniversalFirstOrderThickening`, and
`Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningCoverGluing`, and
`Sheaf.AlgebraicGeometry.UniversalThickeningOpenPieces`.

Added `UniversalFirstOrderThickeningCoverGluing.lean` with a complete proof of
`AlgebraicGeometry.universalFirstOrderThickening_glue` from a geometric glued-atlas assertion.
The proof constructs the transferred test cover using the homeomorphism underlying a test
thickening, proves unique lifting for problems landing in one chart, proves uniqueness for
arbitrary tests, and glues local lifts using that uniqueness. It applies to non-affine tests
and does not assume formal unramifiedness. Its private helpers are all proved.

Added `UniversalFirstOrderThickeningGluedAtlas.lean`, isolating only the construction of the
glued scheme, its square-zero immersion, and its universal open charts. This statement does
not assert the global lifting property and is strictly the geometric part of the argument.
No definitions, existing interfaces, or modules belonging to other workers were changed.
The original node and the two new nodes record the actual proof route.

All three sandbox modules compile in import order with no warnings, each in approximately
2–4 seconds. The final delivery dry run is the mechanical gate.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.FormallyUnramified.exists_affine_local_universalFirstOrderThickening`
(node `lem-weil-pbc-universal-first-order-thickening-affine-local`).
The assigned module has no remaining `sorry`.

Also proved the new public theorem
`AlgebraicGeometry.universalFirstOrderThickening_glue`
(node `lem-weil-pbc-universal-first-order-thickening-cover-gluing`). It has no local hole;
it uses the geometric assertion below.

Added exactly one hole:
`AlgebraicGeometry.universalFirstOrderThickening_gluedAtlas`
(node `lem-weil-pbc-universal-first-order-thickening-glued-atlas`). Its proof is exactly
`by sorry`, in its own module, with its source and complete proof in words in its docstring.
The remaining work is the overlap isomorphisms and cocycle, the scheme glue data, and
identification of the source and square-zero immersion on the glued charts. The global
lifting-property verification has already been completed in the cover-gluing module.

Counts: one original hole closed, one new hole added, net zero. This is a decomposition,
not a claim of a proof independent of sorry. The existing ring existence theorem is also
used as the intended lower dependency; its inherited holes were not added by this delivery.

## No longer needed

No original import was removed. The duplicate square-zero surjectivity proofs in
the assigned and cover-gluing modules are no longer needed; both now reuse the public
open-pieces theorem. No module is pruned. The second reader removed the unused proof imports
`Sheaf.AlgebraicGeometry.UniversalThickeningOpenPieces` and
`Mathlib.AlgebraicGeometry.Gluing` from the new glued-atlas module. These modules
remain available where the proved cover-gluing argument uses them; neither is pruned. The original planned affine-case dependency is used
directly, and the original open-pieces dependency is used in the new cover-gluing proof and
retained in the geometric gluing node. No planned node or module is claimed pruned.

The separate ring uniqueness conjunct is not used, but its public existence theorem is
used, so its module is not pruned. No theorem asserting global existence of a universal
thickening is imported; that would make the construction circular.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned delivery: removed the assigned module’s private
`firstOrder_surjective` and its manual open-base lifting proof. The existing public
`universalFirstOrderThickening_open_pieces` supplies base enlargement; transport
along `s.isoOpensRange` handles an arbitrary open immersion. Removed the duplicate
private `firstOrder_surjective` in the new cover-gluing module as well. Its replacement
`firstOrder_homeomorph` derives the needed topological fact from the existing theorem’s
uniqueness of opens with specified inverse image, rather than repeating its square-zero
ideal-support proof. Both duplicate copies identified in the return are eliminated;
the existing private helper in the library is untouched. No interface changes are needed.

No statement error was found. The assigned node compressed geometric gluing and verification
of the lifting property into one sentence. They are now separate: only geometric gluing
remains open. The existing affine spectrum theorem already handles arbitrary test schemes,
so no additional affine-to-global theorem is needed for an affine chart.

The ring core source module was not in the shared compiled library when first tried. The
available public ring existence theorem provided the required interface. No dependency
module was duplicated or adapted to work around the build state.

The local literature snapshots mentioned in the node were absent. Read the official Stacks
proof at https://stacks.math.columbia.edu/tag/04F3; the new records cite that location along
with the source filename and tag. LeanSearch returned HTTP 500 and is honestly recorded as
unavailable; LeanFinder, Loogle, direct source search, and blueprint search were performed.

The ancestor script printed None for this module-created node. Following the existing
blueprint links resolves the imported ancestor to `thm-weil-pbc-finite-etale-lifting`; the
new nodes record the full intervening chain. The fixed unit route is unchanged.

## New nodes

`lem-weil-pbc-universal-first-order-thickening-cover-gluing` records the proved theorem
combining geometric gluing with the complete local-to-global lifting argument. Its explicit
inputs are universal thickenings on an arbitrary open source cover. It does not assume
formal unramifiedness. Source: Stacks Tag 04F3, last two proof paragraphs. Searches found
only generic scheme-gluing tools, not this theorem.

`lem-weil-pbc-universal-first-order-thickening-glued-atlas` is the sole new hole. It constructs
a first order thickening with a target open cover on which the pullback thickenings are
universal. Source: Stacks Tag 04F3, fourth proof paragraph. It is strictly a geometric
construction, with the final global lifting argument omitted from its conclusion and proved
separately. Empty schemes and empty covers are allowed: the empty scheme supplies the glued
object. No separatedness or affineness of overlaps is assumed; all overlaps are open
subschemes, and the uniqueness argument applies to arbitrary test schemes. Redundant charts,
identity thickenings, and non-separated source schemes require no additional hypotheses.
There are no change records because no existing statement or definition changed.


## Second reading by W4

1. Compared the complete assigned module with the repository using `diff -u`.
   The existing theorem signature and docstrings are byte-for-byte unchanged, as
   are both public imports. All four added imports are proof-only. The other two
   modules are new, and there are no definitions or forced adaptations. The existing
   node changes only `proof`, `proof_deps` and `proof_origin`. Verdict: preserved.
2. Independently compiled all three modules with `lcompile.py --all`: clean,
   approximately 1.9, 3.4 and 3.6 seconds in dependency order. Compiled scratch copies
   with `#print axioms` for the assigned theorem, cover-gluing theorem and atlas
   theorem. Each lists only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`.
   The only delivered `sorry` is the whole proof of the public atlas theorem; there
   is no axiom, unsafe/opaque declaration, external implementation or hollow data.
   Witnesses of the ring and atlas existence statements are eliminated within proofs;
   no definition chooses arbitrary data from an unproved existence theorem.
   Verdict: valid decomposition, one original hole closed and one new hole added,
   net zero; neither public proved theorem is asserted to be independent of sorry.
3. Read the atlas statement and its five-step docstring against Stacks Tag 04F3,
   especially the overlap/cocycle paragraph and the following global lifting
   paragraph. Its hypotheses supply actual local universal thickenings, not their
   existence for the original formally unramified morphism. Its conclusion omits
   global lifting. The proved single-chart lifting, arbitrary-test uniqueness and
   glued-lift helpers supply that missing part; the new hole is strictly a part of
   the argument. Empty source/empty cover yields the empty glued scheme, repeated
   charts use identity transitions, and non-separated sources need only open
   overlaps, not affine overlaps. No extra separatedness, finiteness or affineness
   hypothesis is needed. Independently searched LeanFinder for infinitesimal square
   zero extensions gluing over a Zariski cover, Loogle for `IsClosedImmersion`, and
   grep for infinitesimal/square-zero/nilpotent immersions. Results were generic
   gluing, target-local closed immersions and ring extension tools, not this atlas
   assertion. Direct searches of lean/Sheaf, lean/WeilConjectures and the upstream
   algebraic-geometry source found no duplicate. Verdict: true and suitably split;
   completing the geometric glue data is not a short missing tactic proof.
4. Checked the top-down route: affine ring existence and spectrum universality,
   transport through isoSpec, affine refinement of a pulled-back base cover, open
   base enlargement using the existing open-pieces theorem, geometric atlas, then
   proved lifting on arbitrary tests. Global existence modules would introduce a
   cycle and are not imported. Every current import is used by a statement or an
   explicit proof. Both original proof dependencies remain used; no old dependency
   is omitted from `No longer needed`, and no module is claimed pruned. Inspected
   `dag/units/sk-thm-p1.json` `realized` and the blueprint ancestry: this refinement
   stays below its fixed unit route. Verdict: route retained and imports justified.
5. Matched the three nodes with their Lean signatures and actual dependencies.
   The atlas node records geometric gluing and the sole remaining hole; cover-gluing
   records chart lifting, uniqueness, restriction of kernels and morphism gluing;
   the assigned node records ring/spec transport and the cover reduction. The
   new nodes have source, full proof steps, searches, creation/blueprint metadata
   and matching Lean records. Also read the earlier return: both duplicate private
   `firstOrder_surjective` proofs have been removed. The replacement homeomorphism
   proof uses the existing theorem's uniqueness of inverse-image opens, and the
   base-enlargement helper applies its third clause. Verdict: return repaired.

Second-reading changes: marked the assigned node's final cover-gluing step
non-elementary, since it invokes the substantive new cover-gluing theorem, and
added this independent review. Retained the earlier repair and import pruning
already present in the sandbox; no further Lean change was necessary.
