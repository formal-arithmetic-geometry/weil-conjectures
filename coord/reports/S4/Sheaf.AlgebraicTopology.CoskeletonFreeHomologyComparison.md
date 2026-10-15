## What changed

Proved `CategoryTheory.SimplicialObject.isIso_homologyMap_of_local_surjective_coskeletal`
with its original signature. The proof follows Stacks 01GD with free modules over the given
commutative ring: image-coskeleton factorization, objectwise simplicial homotopy inverses,
free chain homotopies, objectwise detection of quasi-isomorphisms, and exact sheafification.

Added `Sheaf.AlgebraicTopology.ImageCoskeletonFactorization`, containing the proved theorem
`CategoryTheory.SimplicialObject.exists_imageCoskeleton_factorization`. It constructs the
image using `Subfunctor.range` after uncurrying, then applies the actual Mathlib coskeleton
functor. Its private helpers derive the Kan-extension preservation interface from the
existing finite-limit coskeleton theorem. No data is chosen from an arbitrary unproved
existence theorem. All newly constructed objects are explicit; the existential witness
in the finite-limit theorem is used only to prove preservation of right Kan extensions.

Added proof imports for the factorization, chain homotopies, complexes of functors, and
sheaf adjunctions. Updated the original node's proof route and added the proved auxiliary
node. Existing public imports and public signatures are unchanged.

Validation: both delivered modules compiled together, without warnings, using `lcompile.py`.
The final required `deliver3.py --no-push` check is recorded by the delivery tool.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.SimplicialObject.isIso_homologyMap_of_local_surjective_coskeletal`
(node `lem-weil-pbc-coskeleton-free-homology-comparison`).

Also proved the new auxiliary theorem
`CategoryTheory.SimplicialObject.exists_imageCoskeleton_factorization`
(node `lem-weil-pbc-image-coskeleton-factorization`). Both delivered modules contain zero
`sorry`s. Holes closed: 1; holes added: 0; unproved split-offs: 0.

The proof uses the existing declarations `CategoryTheory.truncatedCoskeletonFiniteLimits`,
`SSet.rlp_boundaries_of_coskeletal_map`, and `SSet.exists_section_homotopy_equivalence`.
After rebuilding both sandbox modules, scratch copies with `#print axioms` show that both
public theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. There is no
remaining `sorryAx` in either theorem's proof dependencies.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicTopology.CoskeletalMapTrivialKan` and
`Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits` from the item module. Both remain
necessary through `Sheaf.AlgebraicTopology.ImageCoskeletonFactorization`; neither module
nor its node is pruned from the transitive proof. No module is made unreachable by this
proof. The following old direct `proof_deps` have moved to the auxiliary factorization node:
`def-weil-pbc-sheafification`, `def-weil-pbc-simplicial-object`,
`def-weil-pbc-simplicial-coskeleton`, `def-weil-pbc-trivial-kan-fibration`,
`lem-weil-pbc-truncated-coskeleton-finite-limits`,
`lem-weil-pbc-sheafification-sets-exact`, `lem-weil-pbc-sheaf-sets-mono-epi-iso`, and
`lem-weil-pbc-coskeletal-map-trivial-kan`. All remain transitive dependencies; none is
pruned. No existing public import was removed.

The second reader removed the unused public `Mathlib.CategoryTheory.Sites.Abelian` import
from the new module. Its imports of `Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal`
and `Mathlib.CategoryTheory.Sites.LeftExact` are public because the signature uses
`coskAdj` and the sheafification instance. Other added imports are proof-only.

## Where the brief, the DAG or earlier work was wrong

No statement correction or unit-route departure was needed. The locally surjective map
cannot itself be treated as an objectwise trivial Kan fibration: that property belongs
to the first map of the image-coskeleton factorization. The delivered proof preserves this
distinction.

The named local `literature/stacks-project/hypercovering.tex` file is absent on this shared
checkout. The source proof was checked at the official Stacks page
<https://stacks.math.columbia.edu/tag/01GD>. LeanSearch returned Internal Server Error;
LeanFinder, Loogle, and source searches supplied the available search evidence.

Edge cases: the construction uses no choice of an objectwise homotopy inverse natural in
the site object. Only the original map must be natural, and objectwise detection of
quasi-isomorphisms then applies. Empty section sets and empty sites require no additional
hypothesis. The zero coefficient ring is covered by the same free-functor argument.
The positivity hypothesis is retained exactly as in the original signature.

## New nodes

`lem-weil-pbc-image-coskeleton-factorization`: a proved coefficient-independent factorization
statement covering the geometric first half of Stacks 01GD. Its conclusion consists of
an objectwise trivial Kan fibration followed by a degreewise sheafification equivalence;
it asserts no homology comparison. Its proof uses the existing finite-limit coskeleton
and coskeletal boundary-lifting statements. No new unproved theorem is added.

## Second reading by S4

1. Compared both delivered modules with the repository. The parent theorem is the only
   existing declaration; its signature is byte-for-byte unchanged. Its existing public
   imports, docstring, and visibility are unchanged. The factorization module is new.
   No definition or target statement changed, and no change record is required. Verdict: pass.
2. Compiled both files in dependency order with `lcompile.py --all`, without warnings.
   Searched both files for forbidden declarations and holes: none. Independently compiled
   scratch copies with `#print axioms` for both public theorems: only `propext`,
   `Classical.choice`, and `Quot.sound`. The factorization uses explicit range subfunctors
   and Mathlib's actual coskeleton, not arbitrary data from unproved existence. Verdict: pass.
3. There are no unproved split-offs. Read the new proved factorization theorem in full:
   it establishes only the geometric part of the argument, without asserting homology
   comparison. Checked empty section sets, empty sites, degree one, and the zero ring;
   no nonemptiness or nonzero assumption is introduced. Rechecked Stacks 01GD and searched
   with `msearch.py` using boundary lifting in low degrees, sheafification preservation
   under adjunctions, and image-factorization terms; inspected the library with `rg`.
   Found building blocks already used, not a duplicate factorization/comparison. Verdict: pass.
4. The proof follows the original image-coskeleton, objectwise homotopy, and exact
   sheafification route. The inverses are chosen only objectwise; no unsupported natural
   choice is needed. The free-module homotopy and functor-category homology steps use
   Mathlib directly. Removed the new module's unused Abelian import and corrected the
   visibility of its statement dependencies. The eight old direct dependencies displaced
   by the new factorization are explicitly accounted for above, all still transitive.
   `dag/units/sk-prop-h2.json` has empty realized statement and proof-step lists;
   no fixed unit route is bypassed. Verdict: pass after import cleanup.
5. Read both node files against the Lean proof. Their `proof_deps` equal the unions of
   the proof steps' `uses`; the factorization node's verbatim `lean.statement` matches
   its theorem. Its source, origin, searches, created record, blueprint provenance,
   chapter, unit, status, and Lean record are present. The parent changes only `proof`,
   `proof_deps`, and `proof_origin`, reflecting the actual proof. Verdict: pass.

Second-reading changes: removed the new module's unused public Abelian import; made
its coskeleton and left-exact sheafification imports public as required by its signature;
expanded the pruning inventory; corrected stale claims about the dependency obligations;
added this review. Proof bodies, statements, definitions, and DAG records needed no repair.
