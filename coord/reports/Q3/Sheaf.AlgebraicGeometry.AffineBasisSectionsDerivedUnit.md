## What changed

Replaced the inherited sandbox attempt with a resolution-based proof in
`Sheaf.AlgebraicGeometry.AffineBasisSectionsDerivedUnit`. The existing declaration
`AlgebraicGeometry.affineBasisSections_isIso_derivedUnit` keeps its signature and docstring.
Its proof chooses a K-injective resolution, combines degreewise monicity and epicity of
its evaluated homology maps, localizes the resulting quasi-isomorphism, and cancels the
invertible right-hand factor in the derived-unit naturality square.

Added two proof-only imports, each a separate new module:
`Sheaf.AlgebraicGeometry.AffineBasisSectionsResolutionHomologyMono` and
`Sheaf.AlgebraicGeometry.AffineBasisSectionsResolutionHomologyEpi`.
Their remaining obligations are respectively injectivity and surjectivity on homology,
for a specified resolution and a specified degree. Neither assertion alone proves the
original invertibility statement. Updated the original DAG proof and proof dependencies
to match the complete Lean combination.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.affineBasisSections_isIso_derivedUnit`.

Added two holes in new modules:
`AlgebraicGeometry.affineBasisSections_resolution_homology_mono`
(node `lem-sc-affine-basis-sections-resolution-homology-mono`) and
`AlgebraicGeometry.affineBasisSections_resolution_homology_epi`
(node `lem-sc-affine-basis-sections-resolution-homology-epi`).
There is no sorry left in the item module. This is a decomposition of one hole into
two smaller obligations, not a sorry-free proof of the acyclicity comparison; the
net hole count for this delivery is -1. The resolution choice is local to a theorem
proof; no definition chooses an arbitrary witness of a sorry existence statement.

## No longer needed

No original library import is removed. No original plan dependency is pruned from the
transitive mathematical argument: the affine-basis, restriction, resolution, and Milnor
steps now belong to the new degreewise comparison nodes. The item directly uses only
these two new nodes and `def-pc-ringed-spaces-derived-direct-image`.

The unlanded inherited helper
`AlgebraicGeometry.affineBasisSections_isKInjective_of_acyclicity` and its sandbox-only
node `new-affine-basis-sections-is-kinjective` were removed. The inherited special-case
helper `AlgebraicGeometry.affineBasisSections_isIso_derivedUnit_of_isKInjective` is also
unnecessary: the existing right-derived-functor instance proves invertibility at the
resolution directly. Neither helper was in the original repository module.

## Where the brief, the DAG or earlier work was wrong

The inherited draft confused a K-injective resolution of F with K-injectivity of F
itself. Its new theorem was false: if V is empty, all three basis hypotheses are
vacuous but F is arbitrary on X. Even on a nonempty affine, section acyclicity is
weaker than K-injectivity. The false draft theorem and node are not delivered.
The inherited draft also contained adjacent doc comments that caused a parse error,
and its report counted a newly added special case as an original hole closed.

The original node plan is mathematically consistent with Stacks 08C2, read in
`scratchpad/cohomology.tex`, and 071B (`lemma-K-injective`). Both new statements retain
all three vanishing families and allow an empty affine open, arbitrary integer degrees,
unbounded F, and a resolution J whose terms need not be injective. To compute the
comparison one first uses the special tower resolution and then compares it with J by
a homotopy equivalence over F. For empty V the homology maps are maps between zero
module objects, hence both monic and epic. For i the identity on a K-injective F both
maps are identities. For a zero complex the assertions also reduce to zero homology.

The existing quasi-coherent section-resolution result cannot be imported: it assumes
quasi-coherence and already imports this item. The plan's Milnor and eventually-constant
limit declarations do not construct the required truncation/resolution tower or
identify its section map; the new statements isolate the missing degreewise comparison.

## New nodes

`lem-sc-affine-basis-sections-resolution-homology-mono` records the injectivity half of
08C2 for the section map of an arbitrary K-injective resolution, in one degree.
Its module is `Sheaf.AlgebraicGeometry.AffineBasisSectionsResolutionHomologyMono`.

`lem-sc-affine-basis-sections-resolution-homology-epi` records the surjectivity half.
Its module is `Sheaf.AlgebraicGeometry.AffineBasisSectionsResolutionHomologyEpi`.
Both have source-labelled complete proof sketches, existing mathematical plan
dependencies, and the actual search results from `msearch.py`: LeanSearch was
unavailable; Loogle, LeanFinder and grep returned no exact comparison theorem.
No change record is required: existing statements, definitions, instances, visibility,
and public imports are unchanged. The new modules are imported only by the proof.

## Second reading by Q3

1. The delivered target module was diffed against the repository version. The theorem signature and all existing declarations are unchanged byte-for-byte; only proof-only imports and the proof body were added.

2. Each delivered Lean file was compiled with `lcompile.py`; no compiler errors or warnings occurred. The target has no `sorry`; the only remaining `sorry`s are the two named split-off theorems, each with a docstring and matching DAG node. No axioms, unsafe declarations, hollow definitions, or forbidden implementation features were added.

3. The two split-off statements are the mono and epi halves of the degreewise homology comparison. They are strictly simpler than the target, retain every hypothesis, allow arbitrary degree and empty affine opens, and are sourced to Stacks Tags 08C2 and 071B. Searches found no existing library theorem duplicating either statement.

4. The target proof follows the shortest available derived-category route after the degreewise comparison: choose a K-injective resolution, obtain mono and epi, use the balanced ModuleCat homology criterion, then cancel the invertible derived resolution map by naturality. The proof-only imports are minimal for this route; no old mathematical dependency was removed. The inherited false K-injectivity helper was removed as documented above.

5. The DAG proof and proof dependencies agree with the Lean proof, and the unit route remains realized through the target and its degreewise comparison nodes. The target’s statement is unchanged.

Changed during second reading: added this review section only; no Lean declarations, statements, definitions, or DAG content were altered.
