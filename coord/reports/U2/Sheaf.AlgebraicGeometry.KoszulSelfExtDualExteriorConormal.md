## What changed

Reduced `AlgebraicGeometry.koszulRegularImmersion_self_ext_dual_exterior_conormal`
without changing its signature, universes, hypotheses, public imports or existing docstring.
The proof now obtains a stalk-surjective comparison and proves it injective using the
independent `koszulRegularImmersion_self_ext_stalk_bases` theorem. The determinant pairing,
the regular conormal basis and affine frame supply a surjective map from the exterior of the
restricted conormal dual to the dual exterior conormal. The composite comparison is surjective
between stalk modules with bases on the same finite index set. Mathlib's
`OrzechProperty.bijective_of_surjective_of_injective` makes that composite injective; lifting
along the first surjection proves injectivity of the desired comparison. Stalk conservativity
then gives the sheaf isomorphism.

Added `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalComparisonSurjection`. Its proof glues
compatible local module morphisms on the covering family of chosen neighborhoods using
`SheafOfModules.existsUnique_hom_of_cover`, constructs the global morphism by evaluating the
glued map over the top open, and proves stalk surjectivity by lifting representative sections.

Added `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparison`. This is the remaining
local Koszul calculation and overlap compatibility, stated independently with a complete
proof in words. It supplies a neighborhood of each point and local maps, equal on every
smaller overlap open and surjective on sections on every smaller open. It asserts no global
morphism or global isomorphism. The resulting reduction discharges both global gluing and
injectivity in actual Lean; it does not merely apply an isomorphism under another name.

Updated the DAG to follow these three layers. All new declarations are public module
statements; proof-only imports are nonpublic. No definitions, target statements, existing
public interfaces, other groups' modules, chapters or unit records were changed.

## Proved and sorry left

Validation: `lcompile.py --all` compiled all three delivered modules cleanly, with no
warnings. The original statement comparison reports no signature changes. All line lengths
and DAG proof-dependency unions were checked. `deliver3.py --no-push` printed OK: the
compiled delivery and preflight passed except for the second reading, which belongs to
the next worker. Nothing was pushed.

Closed the original hole:
`AlgebraicGeometry.koszulRegularImmersion_self_ext_dual_exterior_conormal`
(node `lem-sc-koszul-self-ext-dual-exterior-conormal`). No sorry remains in its module.

Also proved the new global gluing theorem:
`AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_comparison_surjection`
(node `lem-sc-koszul-self-ext-conormal-comparison-surjection`). No sorry remains in that module.
The private section-to-stalk helpers, restriction helper and general gluing helper
`global_surjective_of_local_maps` are proved. The latter keeps derived self-Ext definitions
abstract during the gluing construction, avoiding repeated unfolding of their carriers.

Added exactly one hole:
`AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_local_comparison`
(node `lem-sc-koszul-self-ext-conormal-local-comparison`). Its whole proof is `:= by sorry`.
There is no sorry inside any definition or private helper.

This is a decomposition: one original hole closed and one lower hole added, hence net zero
holes removed by this delivery. The existing independent stalk-bases theorem is proved in the current repository,
but depends on the still-holed
`AlgebraicGeometry.koszulRegularImmersion_self_ext_pullback_local_frame`.
Both are reused, not copied or counted as proved by this delivery. The local comparison
is strictly a part of the argument: it supplies compatible maps on a cover, while the
new gluing theorem proves the global map and the original theorem proves injectivity.

Edge cases checked mathematically: for n=0 the local map is the quotient unit; for n above
the local sequence length both local modules vanish. Empty V gives an empty neighborhood
family and a covering sieve of the empty top open, with no stalk obligations. On overlaps,
length equality is checked at a nonzero local ring and then after refinement; there is no
affine-intersection, quasi-separatedness, Noetherian or global rank hypothesis.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.RingTheory.KoszulProjectiveResolution`
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`
- `Sheaf.RingTheory.KoszulGeneratorChainMap`

Their nodes remain needed in the local-comparison module:
`new-j3-koszul-projective-resolution`,
`lem-sc-affine-quotient-resolution-sheafification`,
`lem-sc-derived-internal-hom-restrict-open`,
`lem-sc-derived-hom-finite-free-model`, and
`new-q2-koszul-generator-chain-map`. This is relocation of proof dependencies, not pruning
of their modules from the targets' closure. `lem-sc-koszul-conormal-basis` and
`lem-sc-affine-conormal-frame` are still used directly by the original theorem.
No original dependency node or module is claimed globally pruned.

The inverse-gluing part of the original node's proof is no longer needed: only local maps
are supplied and glued, and the inverse is constructed by `asIso` after stalk injectivity
is proved. Neither `KoszulSelfExtExterior` nor `KoszulSelfExtYonedaSurjection` is imported;
both already depend on the original module, so using them here would create a cycle.

## Where the brief, the DAG or earlier work was wrong

The listed APIs resolve and sheafify the Koszul quotient and compute derived Hom, but none
states the compatible local sheaf maps from the dual exterior conormal. That construction
is the new local-comparison item. The existing generator-chain-map theorem's stated
component formula is only in degree minus the sequence length, whereas the planned self
Ext calculation needs the formula in every degree. Its contraction formula and construction
pattern are available; the all-degree exterior component formula and compatibility remain
explicitly inside the new local comparison's proof in words, not silently assumed proved.

The shorter-looking exterior self-Ext route is circular, as checked by import direction.
The independent stalk-basis route is acyclic. LeanFinder and source searches found no
existing compatible local map statement; LeanSearch returned Internal Server Error.
The source calculation was checked against Stacks [0BQY](https://stacks.math.columbia.edu/tag/0BQY)
and [062I](https://stacks.math.columbia.edu/tag/062I). Gluing was checked against
[03EM](https://stacks.math.columbia.edu/tag/03EM) and
[04TQ](https://stacks.math.columbia.edu/tag/04TQ). The module-sheaf gluing API was read
in full, along with its node `lem-pur-sheaf-hom-cover-gluing`.

## New nodes

`lem-sc-koszul-self-ext-conormal-local-comparison`, in
`lean/Sheaf/AlgebraicGeometry/KoszulSelfExtConormalLocalComparison.lean`, is the remaining
local calculation and overlap compatibility. It retains the original seven Koszul
calculation dependencies, source, unit and blueprint route. Searches and edge cases are
recorded in its node and docstring. Its neighborhood data are used only inside proofs;
no arbitrary witness is used to define a library object.

`lem-sc-koszul-self-ext-conormal-comparison-surjection`, in
`lean/Sheaf/AlgebraicGeometry/KoszulSelfExtConormalComparisonSurjection.lean`, is proved
from the local comparison and the existing generic sheaf-module morphism gluing theorem.
Its DAG records the latter as a generic tool use, not a change of the Picard unit's route.
No change record is needed: all existing signatures and public imports stay identical,
and every added module is new.

## Second reading by U2

1. Interface: PASS. Read the complete diff of the existing module against the
   repository. Its existing theorem signature, universes, hypotheses, conclusion,
   docstring and public imports are byte-for-byte unchanged. The declaration-table
   comparison reports no statement or interface changes. The two comparison modules
   are new; no existing definition or other group's module is edited.
2. Proof: PASS as a decomposition. Compiled all three delivered files locally in
   import order without errors or warnings. Independently printed axioms for all
   three public theorems in scratchpad/lean/Review.lean: each uses only propext,
   Classical.choice, Quot.sound and sorryAx. The only delivered sorry is the whole
   named local-comparison theorem, with its node and proof docstring. There are no
   forbidden declarations and no holed definitions. All witnesses are destructured
   inside proofs; none defines an arbitrary library object. Read both germ-lifting
   helpers, restriction naturality, cover construction and gluing naturality.
   The finite-module criterion applies to the composite on the common finite basis
   index; lifting source elements along q proves the required injectivity.
3. Split statements: PASS. Read their signatures, docstrings and nodes, together
   with the imported resolution, sheafification, derived-Hom and generator-map
   statements. The local assertion constructs compatible maps and section lifts;
   it asserts no global isomorphism and leaves global gluing and injectivity to
   actual proofs. Its section surjectivity on arbitrary subopens is justified by
   the local sheaf isomorphism, rather than by exactness of sections. Checked n=0,
   n greater than local rank, m=0, empty V, and changes of generators after refining
   around a point of an overlap. The zero-differential Hom calculation in Stacks
   0BQY and the conormal identification in 062I support the stated construction.
   Repeated searches with different words: LeanFinder query
   "Ext algebra regular embedding natural exterior normal bundle local Koszul
   resolution" returned cotangent and smoothness results, with no self-Ext map;
   Loogle query '"Ext", "exterior"' returned exterior-algebra APIs only. Source
   searches for Ext/exterior, regular Ext, self_ext and conormal comparison found
   no acyclic replacement. The existing local-frame result supplies a frame but
   no compatible comparisons on overlaps. The remaining hole is not a calculation
   that can be closed in a few minutes from the available declarations.
4. Route and pruning: PASS. The comparison plus independent stalk ranks supplies
   a real reduction, not a new name for the original isomorphism. All five removed
   old direct proof dependencies are listed under No longer needed and remain in
   the local-comparison module; no global pruning is claimed. Each added direct
   proof import supplies a named declaration used in the proof. Public imports of
   the new modules support their signatures; proof-only imports are plain imports.
   The Picard-duality unit and chapter are unchanged. Its realized statement and
   step slots are already empty in the repository; this delivery neither changes
   them nor bypasses a node recorded there. Generic morphism gluing is recorded as
   a tool use, and the original finite-duality ancestry remains.
5. DAG: PASS. All three Lean signatures match their node lean.statement verbatim,
   and each proof_deps set is exactly the union of its proof steps' uses. The new
   nodes contain source, proof, proof_origin, searches, creation, blueprint,
   chapter, unit and Lean records. The parent records comparison construction,
   determinant pairing and independent stalk bases exactly as used by Lean.

Second reading changed the report's stale assertion that the stalk-bases theorem
itself remains holed: it is now proved upstream in this repository, while its
local-frame dependency remains holed. Added this independent review and its
validation evidence. No Lean proof or node required repair. One original hole
is closed and one local hole is added, so this remains a decomposition with net
zero holes removed; the new gluing theorem is proved from that local hole.
