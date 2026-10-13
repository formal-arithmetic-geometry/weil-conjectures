## What changed

Proved `Algebra.localized_fibre_dimension_le_of_basicOpen` in
`Sheaf.RingTheory.FibreDimensionLocalizedBound`, preserving its entire signature and
visibility. Added three proof-only imports:
`Mathlib.RingTheory.Localization.BaseChange`,
`Mathlib.Topology.LocalAtTarget`, and
`Sheaf.Topology.DimensionSupremumLocalDimensions`. All original public imports remain
necessary for the statement.

The proof identifies the localized fibre with the localization of the original fibre
at `1 ⊗ g`. The localization spectrum is an open subspace. The inverse fibre-prime
equivalence contracts along the right tensor inclusion, allowing the given bound to
be reindexed at the fixed base prime. Pulling back open neighbourhoods along the two
homeomorphisms bounds local dimension, and the existing dimension-supremum theorem
bounds global dimension. Two fully proved private helpers provide the inducing-map neighbourhood
comparison and the fibre reindexing; neither changes the public interface.

Updated only `proof`, `proof_deps`, and `proof_origin` of
`lem-weil-pbc-fibre-dimension-neighborhood-localized-bound` to record this argument
and its actual existing dependencies. No new nodes or interface changes.

Sources read: the Mathlib implementations of the fibre equivalence, localization
base change and localization spectrum embedding; the source-library open-subspace
local-dimension theorem; and the already proved Sheaf dimension-supremum theorem.
The local Stacks TeX files are absent on this machine, so the source tags were read
on the official Stacks site:
[00DK](https://stacks.math.columbia.edu/tag/00DK),
[00DL](https://stacks.math.columbia.edu/tag/00DL),
[00E4](https://stacks.math.columbia.edu/tag/00E4), and
[0B7I](https://stacks.math.columbia.edu/tag/0B7I).
Searches actually run through `msearch.py`: LeanFinder for the dimension bound under
fibre localization, Loogle for `PrimeSpectrum.localization_away_isOpenEmbedding`,
and grep for the dimension-supremum and tensor-localization declarations. Local
`rg` searches found the existing theorem and a comparable private homeomorphism helper.
The repair additionally searched for inducing-map local-dimension comparisons and found
Mathlib restriction and global-dimension monotonicity lemmas.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.localized_fibre_dimension_le_of_basicOpen`
(node `lem-weil-pbc-fibre-dimension-neighborhood-localized-bound`).
No holes remain in the item. No holes added, no statements split off.
The existing dimension-supremum theorem used by the proof is already fully proved.
The axiom check reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The module compiles without errors or warnings using `lcompile.py`.

Edge cases: the proof does not use the nontriviality assumption, so an empty localized
fibre has the empty supremum equal to bottom and satisfies the same bound. It also
works at `d = 0`; no positivity or nonzero-element assumption is used. All original
hypotheses, including finite type and nontriviality, are retained verbatim.

## No longer needed

No imports removed: the original file had only its three public statement imports.
Removed the planned proof dependency
`lem-weil-pbc-fibre-dimension-neighborhood`, whose module is
`Sheaf.RingTheory.FibreDimensionNeighborhood`. This is the caller of the current
lemma and is not used or imported here. The removal is a pruning of this proof
edge, not a claim that the caller leaves the targets' global closure.

All substantive steps of the original localized-fibre argument remain. The
replacement dependencies are the existing base-change and spectrum Mathlib leaves,
the fibre-prime Mathlib leaf, the proved open-subspace comparison, and the proved
supremum formula. None of the unit's realized statement or steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item's original sole `proof_deps` entry was
`lem-weil-pbc-fibre-dimension-neighborhood`, but that theorem is proved by applying
this item. Importing it here would close an import cycle. Its statement does not
supply the tensor-localization or local-dimension comparisons needed here. The
updated node lists the actual independent declarations used by the formal proof.

The original prose mentioned a fibre-prime order isomorphism. The formal argument
needs only the equivalence and its explicit inverse contraction, since dimensions
are transported separately along the localization homeomorphisms. No mathematical
statement or definition was changed.

The returned delivery correctly identified the former private helper
`Algebra.dimAt_homeomorph_le` as a duplicate of
`AlgebraicGeometry.localDim_homeomorph_le` in
`Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension`. That declaration is private,
so importing its module cannot expose it by name. Used the requested alternative,
generalizing the helper in place: `Algebra.dimAt_inducing_le` assumes only an inducing
map, rather than a homeomorphism. This is strictly more general: it applies to
inclusions of proper subspaces and to noninjective inducing maps between indiscrete
spaces. Its proof uses Mathlib's `IsInducing.restrictPreimage` and
`IsInducing.topologicalKrullDim_le`; it no longer constructs subtype homeomorphisms.
Both uses in the main theorem pass the homeomorphisms' inducing-map properties.
The helper is fully proved, private, and introduces no hole or interface change.

Updated step 3 of the node to match this generalized comparison. No existing public
signature or visibility changed, and no other module is adapted. Removed the stale
second-reading section of the returned version so the next reader can review this repair.

## Second reading by U1

1. Interface: PASS. Read the repository/sandbox module diff and compared the complete
   existing theorem signature byte for byte, including universes, finite-type and
   nontriviality hypotheses, the fibre-equivalence point and the global dimension
   conclusion. The signature and public visibility are identical. No definitions,
   other modules or change records are delivered; the three added imports are plain
   proof-only imports.
2. Proof: PASS. Independently compiled the delivered module with `lcompile.py`,
   without errors or warnings. Refreshed `scratchpad/axioms.lean` from the repaired
   module (the old scratch copy still contained the superseded homeomorphism helper)
   and compiled its `#print axioms`: exactly `propext`, `Classical.choice`,
   `Quot.sound`, without `sorryAx`. Read both private helper proofs and the main
   argument; scanned for sorry, forbidden declarations and kernel bypasses, finding
   none. There is no arbitrary witness chosen from an unproved existence theorem.
3. Intermediate statements: PASS. No split-off statements, new public declarations,
   new nodes or holes. The inducing comparison follows by pulling back every open
   neighbourhood and applying Mathlib's inducing-map dimension inequality to the
   restriction; neither injectivity nor surjectivity is needed. The fibre helper
   uses the explicit inverse contraction of `preimageEquivFiber`, not an assumed
   compatibility. Checked empty fibres, g = 0 (empty localized spectrum), g = 1
   (the whole fibre), and d = 0: the same argument applies. Independent searches
   of `lean/Sheaf`, `lean/WeilConjectures` and Mathlib, plus msearch grep with
   “inducing local dimension infimum neighbourhood”, found no available public
   replacement for the generalized private helper. Read the previously identified
   private homeomorphism comparison; the repaired helper is strictly more general.
4. Route and pruning: PASS. Read the Mathlib tensor-localization equivalence,
   fibre-prime inverse, restriction theorem and dimension inequality, and the
   existing open-subspace equality and fully proved dimension-supremum module.
   These give a direct proof with no open dependency. Each added import supplies
   a used proof declaration; original public imports support the unchanged
   statement. `## No longer needed` names the sole removed old proof dependency,
   the caller `lem-weil-pbc-fibre-dimension-neighborhood`; it does not claim global
   removal of that caller. Read `dag/units/sk-thm-p1.json`, including `realized`:
   this below-unit comparison changes none of its realized statement or steps.
5. Metadata: PASS. Compared the node diff; only `proof`, `proof_deps` and
   `proof_origin` change. Read every new proof dependency's statement and Lean
   record or Mathlib match. The union of the proof steps' uses is exactly the
   five recorded dependencies, and all are used in the formal argument. The
   tensor-factor conventions agree via the documented tensor symmetry. No
   statement/definition changes or new-node metadata are needed.

Changes by this reader: refreshed the stale scratch axiom-check copy and added
this independent review. The delivered Lean proof and node required no further
change. Closed hole: `Algebra.localized_fibre_dimension_le_of_basicOpen` (1 of 1).
Added holes: none. Split-off statements: none.
