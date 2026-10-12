## What changed

Filled the proof of `AlgebraicGeometry.Scheme.Modules.local_finiteFree_homology_comparison`
in `Sheaf.AlgebraicGeometry.FlatModelFiniteFreeComparison`, preserving its signature and
both public imports. Added proof-only imports for bounded-above flat K-flatness, K-flat
pullback, preservation of quasi-isomorphisms, tensor closure, and flat coproducts.
Private helpers prove flatness of finite-free terms, identify ordinary and tensor
pullback by uniqueness of left adjoints, and transport K-flatness and quasi-isomorphisms.
The final proof takes homology of the pulled-back eP and composes with pullback composition.
Updated the comparison node's proof and dependencies to this actual route.

Added `Sheaf.AlgebraicGeometry.AffineFlatModuleTensorFlat` for the missing flatness bridge.
It assumes the full affine-subopen condition of IsFlatOver and requires no quasi-coherence.
Checked the empty scheme and zero sheaf: the stalk proof remains valid, with no extra
nonemptiness, positive rank, flat morphism, or nonzero-complex assumption.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.local_finiteFree_homology_comparison`
(node `lem-pc-flat-model-finite-free-shortening-comparison`); no sorry remains in its module.
Added one hole: `AlgebraicGeometry.isFlat_of_affineFlatOver_identity`, node
`lem-pc-affine-flat-module-tensor-flat`, in the new module. This is a decomposition,
not a complete axiom-free proof or positive net hole count: one closed and one added.
Existing imported K-flat and tensor lemmas can themselves still depend on named sorries.
The new lemma concerns one sheaf and contains no complexes, quasi-isomorphisms, morphism g,
or homology comparison; it is strictly a proper part of the argument.
Both delivered modules were compiled locally without warnings. The resumed session also
scoped elaboration options to individual declarations so they do not change the public
command environment and explicitly disabled
autoImplicit in the new module. The final delivery dry run printed OK: compilation
and preflight passed except for the second reading, which the second reader supplies.
Nothing was pushed.

## No longer needed

Removed proof dependency `lem-pc-flat-model-finite-free-shortening-construction`
(module `Sheaf.AlgebraicGeometry.FlatModelFiniteFreeConstruction`) from this comparison
node. Its output is already supplied in the comparison's hypotheses, so this module
never needs to import or call the construction theorem. The parent shortening theorem
still uses that construction; this is pruning of this node's dependency, not a claim
that the construction module is globally unreachable.
Removed the construction proof import; both public imports support the unchanged statement.
The second reader removed the redundant explicit import of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`, already publicly
re-exported by DirectImage.Basic. All remaining proof imports support the proof
or its required category instances.
The Q resolution, its quasi-isomorphism and C's lower bound are unnecessary for this
comparison once eP and the structural data are supplied; the existing signature is kept.

## Where the brief, the DAG or earlier work was wrong

The DAG cited the construction as its only proof dependency, although eP is already
supplied. The real step is pullback preservation between K-flat complexes.
The existing `IntrinsicFlatModuleTensorFlat.isFlat_of_isFlatOver_identity` assumes
quasi-coherence, which this module does not assume, so it cannot supply the bridge.
The full IsFlatOver affine-subopen condition does imply tensor flatness without it:
for fixed affine V the stalk is a filtered colimit of flat O(V)-modules, then flatness
passes to O_x by localization. No assertion that G_x is the localization of G(V) is used.

Attempted a direct proof of the bridge using local injectivity of presheaf tensor on
affine opens and the monoidal sheafification comparison. The attempt reached the
flat scalar-structure identification and tensor naturality glue, but its elaboration
exceeded the single-file time limit. It is preserved as scratch work outside lean/;
the delivery retains the named public whole-proof hole with a complete stalk argument.
Stacks Tags 05NE and 00H9 were checked online; the local literature checkout on this
machine contains citation inventories rather than the full Stacks source.

## New nodes

`lem-pc-affine-flat-module-tensor-flat` is the affine-section-flatness to tensor-flatness
bridge, stated in `Sheaf.AlgebraicGeometry.AffineFlatModuleTensorFlat`. It generalizes
an existing quasi-coherent bridge because the supplied comparison has no quasi-coherence
hypothesis. Its docstring and node give the full filtered-colimit, localization and
stalkwise-exactness proof. No existing statement, definition or public visibility changed.

## Second reading by W2

1. Compared the whole comparison module with the repository version using diff.
   Its existing theorem signature, universes, visibility and both public imports
   are byte-for-byte unchanged. In particular C's bounds and affine flatness, Q's
   bound and finite-free terms, e and he, the point t, V <= U, all four structural
   clauses for P, and the supplied eP and heP remain present; the conclusion still
   quantifies over arbitrary g and natural degree q. No existing definition changes
   and no change record is required. Restored the original declaration docstring
   that the first worker had shortened.
2. Independently compiled both delivered modules with lcompile.py --all: clean.
   Read every helper and the final proof: finite-free terms are coproducts of the
   unit, flatness passes along their isomorphism, boundedness gives K-flatness,
   restriction preserves it, and pullback preserves the supplied eP between K-flat
   complexes. The Arrow isomorphism uses naturality in the correct direction;
   pullbackComp then identifies the final homology object. Scratch copies with
   #print axioms for every declaration show only propext, Classical.choice,
   Quot.sound, plus sorryAx for the bridge and the proofs using existing open
   K-flat results. In particular tensorOrdinaryIso has no sorryAx: its adjunction
   choice is backed by a proved theorem, not arbitrary data from an open existence
   claim. There is no axiom/unsafe/opaque/extern/implemented_by or hollow definition.
   The only delivered sorry is the entire named affine-flatness bridge theorem.
3. Read the bridge statement, docstring, node and the definition of IsFlatOver.
   Its full affine-subopen hypothesis really supplies a diagram of flat O(V)-modules
   on affine neighbourhoods of x within V. Restriction maps are O(V)-linear; this
   filtered basis computes G_x. Localization then gives flatness over O_x, without
   identifying G_x with a localization of G(V). Stalk tensor compatibility and
   stalkwise exactness prove tensor exactness. Checked the empty scheme, zero sheaf,
   affine schemes and rank-zero free terms: no missing nonemptiness, quasi-coherence
   or positive-rank assumption. Independently read Stacks
   [05NE](https://stacks.math.columbia.edu/tag/05NE),
   [00H9, Lemma 10.39.3](https://stacks.math.columbia.edu/tag/00H9) and
   [00HT](https://stacks.math.columbia.edu/tag/00HT).
   Searched with LeanFinder "tensor exactness of sheaves from flat modules on a
   basis of opens", Loogle "Module.Flat, IsLocalization", and rg over both library
   roots using stalk/sections/basis/localization and flatness. Results give module
   tensor exactness and Module.flat_iff_of_isLocalization, not this sheaf bridge.
   IntrinsicFlatModuleTensorFlat requires quasi-coherence, absent here; FlatSheafStalk
   proves the other direction. The existing filtered-colimit, localization, stalk
   tensor and stalk exactness nodes cover the bridge's component steps. This one
   added hole is strictly smaller than the comparison, not a renaming of it.
   The unfinished scratch attempt needs substantial scalar and sheafification
   identifications, so this reading leaves the documented bridge hole open.
4. Reviewed from the comparison downward. The proof uses supplied eP directly;
   calling the construction theorem would redo data already in the hypotheses.
   The one old proof_dep is exactly the construction node, and No longer needed
   names it and its removed import completely. The parent shortening theorem still
   supplies that construction, preserving the Mumford-complex step of the unit.
   Read dag/units/sk-thm-picard-coherence.json: its realized statement and step lists
   are empty, and this delivery neither changes nor bypasses any realized node.
   All new imports are proof-only. Removed the redundant explicit Abelian import,
   since the unchanged public DirectImage.Basic import already re-exports it.
5. Compared the existing node JSON to its repository version: only proof,
   proof_deps and proof_origin change. The three steps match finite-free/flat
   K-flatness, left-adjoint comparison and K-flat restriction, and quasi-isomorphism
   preservation followed by homology. The dependencies name exactly those results;
   their statements were read, including coproduct flatness and pullback preservation.
   The new node carries its self-contained hypothesis and conclusion, source,
   proof steps, dependency union, searches, creation/blueprint/chapter/unit metadata
   and the Lean declaration record. Its source argument agrees with the public
   whole-proof sorry. Verdict: valid decomposition, one original hole closed and
   one strictly smaller hole added; no claim of positive net hole progress.

Second-reading changes: restored the existing theorem docstring, added source and
blueprint information to the new module docstring, removed the redundant Abelian
proof import, and wrote this independent review. No mathematical interface changed.
