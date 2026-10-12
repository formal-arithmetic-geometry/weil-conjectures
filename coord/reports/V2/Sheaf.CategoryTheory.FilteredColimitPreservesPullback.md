## What changed

Kept the signature of `CategoryTheory.filteredColimit_preservesPullback` unchanged.
Its proof constructs the limiting image pullback cone using existence of a
mediating arrow and joint monicity of the two projections. Mathlib's
`PullbackCone.isLimitMapConeEquiv` and
`preservesLimit_of_preserves_limit_cone` then give preservation.

Added proof-only imports of `Sheaf.CategoryTheory.FilteredColimitPullbackLift`
and `Sheaf.CategoryTheory.FilteredColimitPullbackHomExt`. Each new module states
one strictly partial assertion of the original argument. Updated the original
node's proof route to those two assertions. The original public imports stay
because its statement uses their declarations.

## Proved and sorry left

Closed the one original hole in
`CategoryTheory.filteredColimit_preservesPullback`. This is a decomposition,
not a proof independent of `sorry`: two lower holes are added, so the delivery's
net hole change is minus one.

The two remaining holes, each in a new module, are:

- `CategoryTheory.filteredColimit_pullback_exists`
  (`lem-weil-pbc-filtered-colimit-pullback-exists`): existence and both
  factorization equations, without uniqueness.
- `CategoryTheory.filteredColimit_pullback_hom_ext`
  (`lem-weil-pbc-filtered-colimit-pullback-hom-ext`): joint monicity, without
  existence of a factorization for arbitrary cones.

No holes remain in the item's module. All three modules compile cleanly using
`lcompile.py --all`. The chosen mediating arrow is determined uniquely by the
joint monicity theorem; the choice from existence occurs only inside the proof
of preservation, and no definition with arbitrary unproved data is added.

## No longer needed

No imports removed and no existing nodes globally pruned. The old direct
proof dependency `lem-weil-pbc-filtered-colimit-sets-elementwise` is replaced
by the two new nodes and remains a proof dependency of both lower arguments.
The other old direct proof dependency `def-weil-pbc-category-colimit` is no
longer used directly by the proof; it remains a statement dependency of the
original node and both new nodes. Neither old dependency is globally obsolete.
`FilteredColimitCategoryFiniteLift`, `FilteredColimitCategoryListEquality` and
`FilteredColimitCategoryDescent` were inspected but not imported: their
signatures require the normalized chosen object colimit rather than an
arbitrary cocone category. These existing results remain potential tools for
proving the two new assertions after transporting along the object-colimit
bijection; this delivery makes no global pruning claim about them.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's finite lifting existence and uniqueness
steps are substantial; they are now explicit separate Lean assertions. Neither
assertion is the original preservation statement under another name.

The source paragraph was read at https://stacks.math.columbia.edu/tag/09YL.
The local `literature/stacks-project/sites.tex` file is absent on this machine.
The source's displayed Hom calculation separates surjectivity and injectivity
of the canonical map to the fiber product. These are the existence and joint
monicity assertions stated here. The source works with a cofiltered index and
contravariant transition convention; the Lean diagram uses a filtered index
and covariant transitions, as the original module already did.

Edge cases checked: filteredness includes nonemptiness; no global pullbacks
are assumed at any stage or in the colimit; the two assertions concern only
this fixed stable cospan. Empty cocone categories have no W, so the quantifiers
are vacuous. For a one-object index the assertions are the ordinary pullback
universal property. Joint monicity is asserted only for maps into the image
pullback object, not for either projection individually.

## New nodes

`lem-weil-pbc-filtered-colimit-pullback-exists` records finite lifting of a
compatible pair followed by the preserved stage pullback's existence property.
Its module is `Sheaf.CategoryTheory.FilteredColimitPullbackLift`.

`lem-weil-pbc-filtered-colimit-pullback-hom-ext` records lifting two candidate
arrows and their projection equalities followed by stage uniqueness.
Its module is `Sheaf.CategoryTheory.FilteredColimitPullbackHomExt`.

Both nodes use Tag 09YL and the existing filtered-set-colimit Mathlib leaf,
include complete natural-language proofs, and record LeanFinder, Loogle and
local text searches. The unit route is kept: neither node bypasses a unit's
statement or proof step.


## Second reading by V2

1. **Interface: pass.** Compared the delivered item with the repository using
   `diff -u`; only two plain proof imports and the original theorem's proof
   changed. Its signature and docstring are byte-for-byte unchanged. The two
   other modules and nodes are new; no definition or existing statement changed,
   and no change record or forced adaptation is needed.
2. **Proof and axioms: pass as a decomposition.** Independently compiled all
   three modules with `lcompile.py --all`. A scratch copy with `#print axioms`
   for all three declarations reports only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` (the latter comes from the two reported holes).
   Inspected every delivered declaration: exactly the two public named whole
   theorem proofs remain `sorry`; no definition, forbidden axiom, or unchecked
   implementation was added. The existence witness is chosen locally inside
   the theorem proof, and joint monicity supplies uniqueness.
3. **Split statements: pass.** Existence with both factorization equations and
   joint monicity are strictly separate parts of the universal property, not
   renamed preservation assertions. Both are true by finite stage lifting and
   eventual equality followed by the stable stage pullback universal property.
   Checked the discrete singleton index, constant identity diagram, empty
   categories (where any quantified vertex is impossible), and nonfaithful
   transition functors (equalities need only hold eventually). No global
   pullbacks are silently assumed. Read the source Hom calculation at
   https://stacks.math.columbia.edu/tag/09YL and the equality criterion at
   https://stacks.math.columbia.edu/tag/04AX. Fresh LeanFinder, Loogle, and grep
   searches used joint monicity and factorization vocabulary; they found general
   monomorphism results and `PullbackCone.IsLimit` constructors/eliminators,
   not an existing theorem for the arbitrary cocone in this item. Inspected
   local finite-lift, list-equality, and descent declarations: they require
   the normalized chosen object colimit, so applying them here needs transport
   of the category structure and cocone. Neither lower hole closes by a short
   application of those results. Both docstring proofs and node records exist.
4. **Route and pruning: pass.** Read the proof top down: existence and joint
   monicity construct the mapped limiting cone through `isLimitAux'`; Mathlib
   then transfers that witness and proves preservation. Every public import
   supplies names in the statement; both added imports are plain proof imports.
   All old proof dependencies are now explicitly accounted for under
   `## No longer needed`. Checked `dag/units/sk-thm-p1.json` and its `realized`
   statement and steps: this is a refinement below the unit level, and none
   of those realized nodes is bypassed or changed.
5. **DAG agreement: pass.** The original node's three steps and two proof
   dependencies match the two helper applications and the Mathlib universal
   property argument. Each new node has its source, complete proof plan,
   dependency union, searches, creation and blueprint provenance, chapter,
   unit, and verbatim Lean signature. No existing node fields outside the
   stage-3-owned proof fields were changed.

Second-reading changes: clarified the status of both former direct proof
dependencies in `## No longer needed` and added this independent review.
No Lean proof or statement needed repair. This closes one original hole by
adding two simpler holes: a decomposition, with net holes closed minus added
of -1, and no module pruning.
