## What changed

Replaced the proof of
`AlgebraicGeometry.Etale.exists_higherDirectImage_affine_section_eq_zero`
without changing its signature or existing docstring. The proof obtains a local-zero
covering sieve, extracts a finite subcover using affineness of V, synchronizes the
local transition arrows with `IsFiltered.wideSpan`, transports zero by naturality,
and applies sheaf separatedness. Separatedness is applied to the homomorphism from
lifted integers sending 1 to the transported section, so no concrete-sheaf universe
comparison is needed.

Added `Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing`, containing
one public intermediate theorem for the local cohomology-comparison portion of
steps 1 and 2 of the original plan. Its conclusion gives a covering sieve with
independently varying later zero witnesses; it asserts neither a finite subcover
nor a common stage nor vanishing of the original section over V. The main proof
performs those remaining steps. The local theorem works for arbitrary etale V and
omits the unused colimit assumption on K.

Updated the parent DAG proof and dependencies to match the Lean proof. The new
node inherits the original local comparison route and its two mathematical inputs.
No unit or chapter route is bypassed; the unit's realized fields are empty, and
both original proof dependencies remain below the local theorem.

Both sandbox modules compile cleanly with `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.exists_higherDirectImage_affine_section_eq_zero`
(node `sbc-lem-higher-direct-image-affine-section-vanishing`), from the local lemma
and a complete finite-cover argument. No sorry remains in the assigned module.

Added exactly one hole:
`AlgebraicGeometry.Etale.exists_higherDirectImage_local_section_eq_zero`
(node `lem-sbc-higher-direct-image-local-section-vanishing`), in its own new module.
Its proof is exactly `:= by sorry`. Its docstring gives the cohomology representative,
base-change continuity, and sieve-generation argument, with sources.

This is a decomposition: one upper hole closed and one lower hole added, net zero
holes removed. It is not a sorry-free proof of cohomology continuity or of the
project's targets. The compactness, finite synchronization, naturality, and
separatedness portion is now proved in Lean.

Edge cases checked mathematically: for empty V, the empty covering is permitted
and sheaf separatedness forces the section to be zero; `wideSpan` still has the
initial object i even for an empty family. For a singleton index category the
canonical comparison is an isomorphism and the identity witness suffices. For
p = 0 the local lemma reduces to ordinary section continuity. No compactness of
S or of an arbitrary V in the local lemma is assumed: affine refinements provide
the qcqs objects to which cohomology continuity is applied.

## No longer needed

Removed the assigned module's direct proof imports of
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf` and
`Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`, replacing them with
`Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing`.
The two removed imports are retained in the new intermediate module as its planned
proof dependencies. Thus no original dependency node or module is pruned from the
transitive target closure, and no claim of transitive pruning is made.

Second reading removed the redundant direct proof imports
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` and
`Mathlib.CategoryTheory.Filtered.Basic`: the required openness and filteredness
declarations are already available through the retained imports. A scratch copy
without both imports compiled cleanly. No additional DAG node was pruned.
Public imports and the original declaration's statement are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan omits substantial Lean glue:
the public abelian higher-direct-image presheaf theorem supplies an existential
isomorphism, while the local step needs its compatibility with the canonical
maps and the identification with cohomology after relative base change. The
complex-continuity theorem is stated for absolute schemes and systems of complexes,
so its application also needs base-change and degree-zero comparison data.
These are precisely the local portion left to the new item, not an assumption
that continuity of K as a sheaf diagram is already known.

Searches found no direct shortcut. The module-coefficient affine-continuity lemma
assumes a fixed pulled-back sheaf, and the eventual-zero lemma for sheaf colimits
assumes the comparison cocone is already a colimit. Neither applies to this
varying abelian-coefficient system. LeanSearch returned an internal server error;
LeanFinder and grep searches ran and found no matching theorem. A Loogle search
for `CategoryTheory.Presheaf.IsSheaf` returned generic sheaf lemmas. The blueprint
searches for higher direct images and eventual vanishing found no duplicate of
the new local statement.

The local Stacks source checkout is absent on this machine. Read the official
pages for Tags 09Z1 and 03Q8, and obtained their TeX labels from the repository's
`literature/stacks-tags-cited.tsv`. The route follows those sources and the existing
0EZM dependency's recorded proof.

## New nodes

`lem-sbc-higher-direct-image-local-section-vanishing`, in
`dag/nodes/sec-smooth-base-change/`, states only local eventual vanishing along a
covering sieve, before compact finite selection and synchronization. Its Lean
module is `Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing`, with
declaration `AlgebraicGeometry.Etale.exists_higherDirectImage_local_section_eq_zero`.
Its proof uses the original `sbc-lem-higher-direct-image-presheaf` and
`lem-weil-pbc-etale-cohomology-limit-complex-systems` dependencies. The latter is
retained as the same generic complex-continuity tool used by the parent plan,
not as a change to the unit route. No statement or definition was changed, so
there is no change record.

## Second reading by A2

1. Interface: PASS. Compared the assigned module with the repository using diff.
   The existing theorem signature and its docstring are byte for byte unchanged;
   only private proof imports and the proof body differ. The other delivered Lean
   module is new and has its own node. No definition, target, existing statement,
   or public import is changed, so no change record is required.
2. Proof and trust: PASS as a decomposition. Both modules compiled cleanly in
   import order with lcompile.py. Scratch copies checked #print axioms for
   exists_higherDirectImage_affine_section_eq_zero and
   exists_higherDirectImage_local_section_eq_zero: each uses only propext,
   Classical.choice, Quot.sound, and sorryAx. The sole textual sorry is the whole
   proof of the public named local theorem reported above; no forbidden declaration
   or hollow definition was found. The finite-subcover, wideSpan factorization,
   naturality, and separatedness argument was read line by line. Evaluating the
   homomorphism from lifted integers at 1 recovers precisely the desired section.
3. Split statement: PASS. Read the entire local lemma and its node and checked
   their agreement. Its covering sieve allows independently varying stage
   witnesses; the assigned theorem still proves finite selection, synchronization
   and global equality, so this is a strict part of the argument, not a renamed
   target. Read the official sources [09Z1](https://stacks.math.columbia.edu/tag/09Z1),
   [03Q8](https://stacks.math.columbia.edu/tag/03Q8), and
   [0EZM](https://stacks.math.columbia.edu/tag/0EZM). Their restricted-cohomology and
   continuity arguments justify the stated local refinement proof. Checked empty
   V, zero sections, a singleton indexing category, and p = 0. Arbitrary V can
   be covered by affines; the qcqs hypotheses are on the structure morphisms,
   giving qcqs base changes over each affine, not an extra hypothesis on S.
   Fresh LeanFinder, Loogle, and grep queries using local injectivity and canonical
   comparison terminology found generic sheafification tools but no duplicate.
   Read EtaleSectionColimitLocalZero, EtaleSectionColimitEventualZeroAux,
   HigherDirectImageAffineContinuity, and EtaleComplexClassVanishing: the first
   results require ModuleCat coefficients and/or an already known colimit; the
   last requires the absolute cohomology presentations that the local comparison
   must construct. Closing this hole needs substantial base-change and naturality
   work, rather than a few-minute application of an existing theorem.
4. Route and pruning: PASS. The proof follows the parent plan's local comparison
   and then proves the compactness and separatedness steps. Both old proof_deps
   are listed under No longer needed as removed direct imports but retained
   transitively in the local lemma, so no transitive module pruning is claimed.
   Read dag/units/sk-lem-failure-field.json: realized.statement and its sole
   realized.steps entry are empty. The existing chapter and unit route is kept.
   Removed two redundant direct Mathlib proof imports after a successful scratch
   compile without them; the declarations remain accessible through imports.
5. DAG: PASS. Parent proof_deps is exactly the new local node; the four parent
   proof steps describe the actual Lean argument. The local node retains the two
   original cohomological dependencies, has its source, full natural-language
   proof, searches, creation and blueprint ancestry, chapter/unit, and verbatim
   Lean signature. Both proof_origin records describe their respective routes.

Changed in second reading: removed the two redundant direct Mathlib proof imports
and corrected No longer needed accordingly; added this independent review.
No proof body, statement, definition, node route, or hole count was changed.
One upper hole is closed and one strictly local hole is added: net zero.
