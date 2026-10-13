## What changed

Replaced the sole sorry in `CategoryTheory.rightDerived_triangle_connecting` with a
complete Lean proof from the existing horseshoe delta-functor and resolution
existence theorems, a fully proved general extension-boundary comparison, and one
new fixed-horseshoe triangle-comparison statement. The existing signature and
visibility are unchanged; its original docstring is unchanged.

Added `Sheaf.CategoryTheory.Abelian.NatComplexDerivedBoundary`. Its canonical
`natComplexDerivedHomologyIso` is an explicit composite of Mathlib isomorphisms,
with no postponed data or proofs. `natComplex_boundary_derived` is fully proved:
extension preserves exactness degreewise, an actual morphism of snake diagrams
identifies the extended boundary, and the cone calculation identifies the
integer-indexed snake boundary with the derived SES triangle boundary.

Added `Sheaf.CategoryTheory.Abelian.HorseshoeDerivedTriangleComparison`. Its
remaining theorem states the comparison of two actual triangles for a fixed
horseshoe, together with the endpoint homology identities. It neither asserts
existence of a delta-functor nor mentions any delta-functor boundary. The main
module applies homology naturality to this triangle morphism and performs the
isomorphism cancellations explicitly; it is not an application of a renamed
version of its original statement.

The new comparison is imported only for proofs. Removed two old proof imports.
Updated the parent DAG proof to the actual four-step Lean argument and added
nodes for both new public theorems. No definitions or existing statements were
changed, so no forced adaptations or change records are needed.

Validation: all three modules compile through `lcompile.py --all` without errors
or warnings. A separate compiler probe of
`#print axioms CategoryTheory.natComplex_boundary_derived` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed the item's one original hole:
`CategoryTheory.rightDerived_triangle_connecting`
(`lem-sc-p1-right-derived-triangle-connecting`). This is a decomposition from
named statements, not a claim of a sorry-free import closure.

Also proved the new general theorem
`CategoryTheory.natComplex_boundary_derived`
(`lem-sc-p1-nat-complex-derived-boundary`), including five private proved helpers:
`integer_boundary`, `extension_shortExact`, `extendOpcycles_naturality`,
`extendOpcyclesToCycles`, and `extension_boundary`.

Added exactly one hole, whose proof is exactly `:= by sorry`:
`CategoryTheory.horseshoe_derived_triangle_comparison`
(`lem-sc-p1-horseshoe-derived-triangle-comparison`). No sorry remains in the
item or in `NatComplexDerivedBoundary`; none is inside a definition or a
private theorem. Net newly closed minus added holes is zero before closure
pruning, while the general boundary comparison is fully established.

## No longer needed

Removed direct proof imports:
- `Sheaf.CategoryTheory.Triangulated.TriangleMorphismExtension`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.

Both modules remain needed transitively: third-map uniqueness is part of the
remaining triangle comparison, and the right-derived-functor module is already
publicly imported through `PlusSingle`. These import removals do not claim that
those modules leave the targets' closure.

The explicit cocycle-only plan node
`lem-weil-pbc-complex-ses-connecting-formula` is no longer needed on this route.
The proved cone/snake comparison replaces that calculation. It had no Lean
module recorded in the repository, so there is no corresponding import to
remove. The degreewise split chain-map and triangle nodes remain needed by the
new comparison; they are not pruned.

The original direct proof dependencies other than the two horseshoe nodes now
occur below the new proved boundary node or the remaining triangle comparison,
or as statement dependencies. This is relocation, not a claim to have pruned
those nodes globally. The updated parent `proof_deps` lists only its actual
new proof's dependencies.


Second reading also removed redundant direct proof imports from
`NatComplexDerivedBoundary`:
- `Mathlib.Algebra.Homology.HomologicalComplexAbelian`.
- `Mathlib.Algebra.Homology.HomologySequenceLemmas`.
These are already available through the retained Mathlib imports; all three
modules compile without these lines. No whole module is pruned from the target
closure.

Complete accounting of the old parent proof dependencies removed from its direct
`proof_deps` (the two horseshoe dependencies remain direct):
- `lem-weil-pbc-degreewise-split-connecting-morphism`: below the triangle comparison.
- `lem-weil-pbc-complex-ses-homology-long-exact`: below the proved boundary comparison.
- `lem-weil-pbc-degreewise-split-derived-triangle`: below the triangle comparison.
- `lem-weil-pbc-complex-ses-connecting-formula`: bypassed by the proved snake comparison.
- `def-weil-abstract-derived-category`: statement dependency and below both comparisons.
- `def-sp-injective-resolutions`: statement dependency and below the triangle comparison.
- `def-weil-triangulated-category`: below the triangle comparison.
- `lem-weil-pbc-bounded-below-injectives-kinjective`: below the triangle comparison.
- `lem-weil-pbc-kinjective-hom-derived`: below the triangle comparison.
- `lem-weil-pbc-triangle-morphism-extension`: below the triangle comparison.
- `lem-sf-derived-ses-triangle`: statement dependency and below the triangle comparison.
- `lem-weil-pbc-derived-direct-image-triangulated`: below the triangle comparison.
- `lem-sf-derived-homology-long-exact`: below the proved boundary comparison;
  the main proof uses Mathlib's defining boundary naturality calculation.
- `lem-sp-derived-functor-single-identification`: statement dependency and below
  the triangle comparison.

## Where the brief, the DAG or earlier work was wrong

Two planned dependencies have no `lean` record or `mathlib_match`:
`lem-weil-pbc-degreewise-split-derived-triangle` and
`lem-weil-pbc-complex-ses-connecting-formula`. Thus the claim that every step of
the original plan already has a usable recorded Lean declaration was inaccurate.
The latter is bypassed by the now-proved general cone/snake argument; the former
is explicitly part of the remaining fixed-horseshoe comparison proof sketch.

The local `literature/stacks-project` source files are absent on this machine.
Read the public Stacks pages instead: [0117](https://stacks.math.columbia.edu/tag/0117),
[011J](https://stacks.math.columbia.edu/tag/011J),
[014Q](https://stacks.math.columbia.edu/tag/014Q),
[05TE](https://stacks.math.columbia.edu/tag/05TE), and
[015B](https://stacks.math.columbia.edu/tag/015B), as well as the pinned Mathlib
cone, homology, extension, and snake-input implementations. The detailed API
argument is marked as written by Q1 in the new nodes rather than attributed
verbatim to a source. LeanSearch returned HTTP Internal Server Error, recorded
as unavailable; LeanFinder, Loogle, and grep were run and recorded.

Edge checks: the proved extension argument explicitly handles every negative
integer degree by zero objects, and its snake comparison includes n=0 with
no missing incoming differential hypothesis. It assumes no degreewise splitting
or injectivity. The remaining comparison uses genuine injective resolutions
and both augmentation squares; row exactness supplies the necessary splitting.
For a split object sequence the boundary is zero on both sides; for the zero
sequence the endpoint equations are identities between zero objects. The
comparison applies to arbitrary compatible resolutions and does not choose
an arbitrary witness as the data of a definition.

The unit `sk-thm-picard-duality` has empty `realized.statement` and
`realized.steps[0]`; this delivery changes neither the unit nor its route. The
original direct horseshoe/cone comparison remains in the new triangle-comparison
node, followed by the explicit homology comparison proved here.

## New nodes

`lem-sc-p1-nat-complex-derived-boundary`, in
`dag/nodes/sec-picard-framework/`, records the general comparison of a
nonnegative complex's snake boundary with the derived triangle of its extension
by zero. Its module is `Sheaf.CategoryTheory.Abelian.NatComplexDerivedBoundary`;
its theorem is fully proved. The same node records the explicit canonical
homology isomorphism used in its statement.

`lem-sc-p1-horseshoe-derived-triangle-comparison`, in the same DAG directory,
records the fixed-horseshoe triangle morphism and endpoint homology identities.
Its module is `Sheaf.CategoryTheory.Abelian.HorseshoeDerivedTriangleComparison`;
this is the sole newly postponed theorem. Its proof sketch contains the
sign comparison, transport by augmentations, termwise evaluation of the derived
functor, and identification with the canonical chosen-resolution isomorphisms.
It preserves the parent's original source route, before the homology naturality
argument that the parent now proves.

No change records were created.

## Second reading by Q1

1. Interface: PASS. Read the full repository/sandbox diff of the item. The only
   changes are its proof, a declaration-local elaboration option, and plain proof
   imports. The existing theorem signature and docstring are byte-for-byte
   unchanged. The other two modules are new. No target, existing definition,
   visibility, or statement changes; no forced adaptations or change records.
2. Proof and trust: PASS. Compiled all three modules locally in import order.
   Inspected every proof and the sole definition: the homology isomorphism is an
   explicit composite, not data chosen from an existence theorem. The only hole
   is the whole public theorem `horseshoe_derived_triangle_comparison`, with its
   source, full proof sketch and matching node. Scratch `#print axioms` checks
   the definition, both new theorems and the item: the definition and proved
   boundary theorem use only propext, Classical.choice and Quot.sound; the item
   and open comparison additionally use sorryAx. No forbidden declarations or
   hidden holes. This remains a decomposition (one closed, one added), net zero.
3. Split statements: PASS. Read both statements, their docstrings and nodes,
   Stacks [0117](https://stacks.math.columbia.edu/tag/0117),
   [014Q](https://stacks.math.columbia.edu/tag/014Q),
   [05TE](https://stacks.math.columbia.edu/tag/05TE) and
   [015B](https://stacks.math.columbia.edu/tag/015B), and the pinned Mathlib
   split-triangle, snake and localization APIs. These sources supply the route;
   the API-specific comparison is the worker's argument. For the open theorem,
   injectivity splits every row; both augmentation equations are present; the
   bounded-below resolution computes Hom from a degree -1 single complex as
   zero. The split map is s then d then pi, with the cone sign accounted for.
   Additivity preserves the splitting and commutes with extension and shift;
   `PlusSingle`'s explicit chosen-resolution isomorphism matches the endpoint
   identities after resolution comparison. For a split sequence both boundaries
   vanish, and for the zero sequence both endpoint equations are zero. The
   proved theorem explicitly covers negative extended degrees and n=0 without
   an extra hypothesis. The open theorem is a structural triangle-comparison
   step, without any delta-functor or boundary assertion; the item additionally
   proves the snake comparison and performs naturality and cancellation. It is
   not the item renamed. Fresh LeanFinder, Loogle and grep searches (different
   queries from the worker), repository and upstream source searches found no
   existing theorem closing this structural comparison in a few minutes.
4. Route and pruning: PASS after repair. Checked the item top down: existing
   horseshoe delta-functor and existence results give its first part; the proved
   general snake/cone comparison and the structural triangle morphism reduce
   its second part to Mathlib boundary naturality and explicit iso cancellation.
   Reviewed `natComplexDerivedHomologyIso` against the `PlusSingle` definitions.
   The new comparison retains the original split/cone/augmentation route.
   `sk-thm-picard-duality.realized` has no assigned statement or step nodes; it is
   unchanged. Public imports support signatures or definition data. Removed two
   redundant plain Mathlib imports; retained imports provide their declarations.
   Completed the report's list of every old direct proof dependency removed,
   distinguishing relocation from closure pruning. No whole-module pruning is
   claimed.
5. DAG agreement: PASS. Compared the parent JSON against the repository: only
   proof, proof_deps and proof_origin differ. Its four steps describe the actual
   Lean argument, and proof_deps is their union. Both new nodes have matching
   verbatim Lean theorem signatures, source/proof/search/provenance records,
   parent chapter/unit and blueprint ancestry. The proved boundary node records
   the constructed isomorphism as well as its theorem. The open comparison node
   retains the genuinely unfinished structural argument and original tools.

Changes by this reading: removed two redundant Mathlib proof imports from
`NatComplexDerivedBoundary`, expanded `No longer needed` to account explicitly
for every removed old direct proof dependency, and added this independent review.
No proof, statement, definition, node or hole was changed.
