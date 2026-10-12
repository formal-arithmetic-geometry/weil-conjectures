## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.exists_finiteLocallyFreeMapIsoOpen` by a compiling
proof with its signature and public imports unchanged. Added three proof-only imports:
`Sheaf.AlgebraicGeometry.ModuleMapIsoLocusPullback`,
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusCompact`, and
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusPullback`.

Constructed `moduleMapIsoLocus` as the supremum of the open subsets on which the
restricted tensor pullback is invertible. This is actual data, with no choice of
an arbitrary witness from an unproved existence theorem. Its membership lemma is proved.
The witness in the item is this open subscheme with its canonical inclusion.
Mathlib's embedding compactness criterion and affine quasi-compactness criterion
convert compactness of its affine intersections into quasi-compactness of the inclusion.
Mathlib's open-immersion lift constructs the required factorization from range containment.

Proved `isIso_tensorPullback_of_range_subset_moduleMapIsoLocus` for arbitrary module
maps, without finite local freeness. The inverse images of all invertibility opens cover
the test scheme. Uniqueness of left adjoints identifies tensor pullback with Mathlib
pullback, and composition identifies the local maps with further pullbacks of invertible
maps. Restriction and over-functor equivalences and Mathlib sheaf locality finish the proof.
This uses existing tensor-pullback adjunction theory, not a new hole.

The two remaining determinant arguments are isolated as named theorems in separate modules.
Every delivered file compiled through lcompile.py, in import order. No axiom, definition hole,
statement change, public interface change, or forced adaptation is introduced.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_finiteLocallyFreeMapIsoOpen`
(node `lem-sc-finite-locally-free-map-iso-open`). The item's module has no sorry left.
This is a decomposition into two new holes, not a complete sorry-free proof or a net
reduction in the hole count.

Added and proved:
`AlgebraicGeometry.Scheme.Modules.mem_moduleMapIsoLocus` and
`AlgebraicGeometry.Scheme.Modules.isIso_tensorPullback_of_range_subset_moduleMapIsoLocus`.
The private tensor/Mathlib pullback comparison is also proved.

Exactly two new sorries remain:

- `AlgebraicGeometry.Scheme.Modules.isCompact_moduleMapIsoLocus_inter`
  (`lem-sc-finite-locally-free-map-iso-locus-compact`), in
  `Sheaf.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusCompact`.
- `AlgebraicGeometry.Scheme.Modules.range_subset_moduleMapIsoLocus_of_isIso_tensorPullback`
  (`lem-sc-finite-locally-free-map-iso-locus-pullback`), in
  `Sheaf.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusPullback`.

Each is strictly a part of the original argument. The first concerns compactness of
an explicitly specified subset on a single affine open; it states no universal property.
The second is only the necessary range-containment implication for an invertible
pullback; it asserts neither compactness nor existence of a representing scheme.
The sufficient implication, the construction, the quasi-compactness conversion,
and the scheme factorization are proved in Lean.

Edge cases checked in the statements and proof plans: empty ambient and test schemes,
rank-zero maps, unequal ranks, locally varying ranks, zero determinant, and nonreduced
rings. Empty test schemes impose vacuous range containment; the general locality proof
also handles the empty cover. Rank zero gives determinant 1. Unequal ranks contribute
empty determinant loci, because any inverse would identify unequal-dimensional residue
vector spaces. No reducedness or global bound on ranks is added.

## No longer needed

No existing imports, nodes, or modules are pruned. All four original proof dependencies
remain necessary transitively: finite local freeness for the determinant lemmas,
tensor pullback for the locus and base change, open immersions for the canonical inclusion
and lift, and quasi-compactness for the affine compactness conversion.

During development removed the redundant QuasiCompact import from the new affine
compactness statement module, and removed redundant imports of
`Mathlib.CategoryTheory.Sites.Spaces` and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` from the new general
pullback module, and verified it still compiled. Its only additional proof import is
`Mathlib.CategoryTheory.Sites.LocalProperties`. No planned but unused project theorem
was imported. In particular the general gluing proof directly uses Mathlib rather than
importing the broader `Sheaf.Topology.SheafIsomorphismLocalOpenCover` dependency tree.

## Where the brief, the DAG or earlier work was wrong

The parent DAG labeled the determinant construction, retrocompactness argument and
arbitrary-base-change criterion elementary while listing only definitions as dependencies.
Those definitions do not themselves supply the matrix/stalk/frame arguments. The delivery
makes two missing parts explicit and proves the general local-gluing part from existing
Mathlib declarations. No mathematical statement was disputed or changed.

LeanSearch returned an Internal Server Error; this unavailability is recorded without
claiming a negative search result. LeanFinder, Loogle, Mathlib/source-library text search,
and blueprint/DAG search found generic ingredients but no exact locus theorem.
Read Stacks Tags 05GD and 0BDP directly. The unit and chapter route are retained; the
unit's realized lists are empty, and the decomposition stays below its original node.

## New nodes

`def-sc-module-map-iso-locus`: explicit supremum construction and its proved membership
criterion, in `Sheaf.AlgebraicGeometry.ModuleMapIsoLocus`. It chooses no unproved witness.

`lem-sc-module-map-iso-locus-pullback`: proved preservation of invertibility under
pullback whose image lies in the locus, for arbitrary module maps, in
`Sheaf.AlgebraicGeometry.ModuleMapIsoLocusPullback`. Uses Mathlib sheaf locality and the
existing tensor-pullback adjunction.

`lem-sc-finite-locally-free-map-iso-locus-compact`: the remaining affine compactness
argument, in `Sheaf.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusCompact`. Its docstring
and node give the finite principal-frame-cover/determinant proof with all edge cases.

`lem-sc-finite-locally-free-map-iso-locus-pullback`: the remaining reflection argument,
in `Sheaf.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusPullback`. Its docstring and node
give the residue-field scalar-extension and adjugate neighbourhood proof.

Updated the parent node's proof, proof_deps and proof_origin to the actual Lean route.
No change record is needed: existing statements, definitions and public imports are unchanged.

## Second reading by K1

1. Compared the existing item's module with the repository by diff. Its declaration
   signature, universe, namespace, visibility, docstring, and public imports are byte for
   byte unchanged. Only its proof and three proof-only imports differ. The four helper
   modules and their nodes are new; no existing definition or statement was changed.
   Verdict: pass; no change record or forced adaptation is needed.
2. Independently compiled all five modules with lcompile.py in import order, without
   errors or warnings. Inspected every definition and proof for prohibited declarations
   and hidden holes. A scratch copy with explicit #print axioms verified that the locus,
   membership lemma, and general preservation theorem use only propext, Classical.choice,
   and Quot.sound. The two declared determinant holes and the parent additionally use
   sorryAx, as reported. The witness is the actual open subscheme of a supremum, with no
   data chosen from a mere unproved existence. Verdict: pass as a decomposition, not a
   completed proof of the original theorem without sorryAx.
3. Read both split-off signatures, docstrings and nodes against Stacks
   [05GD](https://stacks.math.columbia.edu/tag/05GD) and
   [0BDP](https://stacks.math.columbia.edu/tag/0BDP). The finite principal-frame cover and
   determinant argument proves affine compactness without a noetherian assumption.
   For reflection, k(h(t)) injects into k(t); equal residue dimensions and the determinant
   give an inverse on a neighbourhood of h(t). Tested empty schemes, zero rings/empty
   frames, zero ranks, unequal ranks, varying ranks, and nilpotents. Each lemma is a
   strict component, and neither asserts the parent's existential universal property.
   Repeated LeanFinder with a fiber-bijectivity/retrocompactness query, Loogle with
   determinant/unit keywords, and rg with fiber/stalk/bijectivity and open-locus terms.
   Matrix.isUnit_iff_isUnit_det supplies algebra, not either sheaf theorem. Read upstream
   Modules.LocallyFreeAffine (local frames, projective affine sections) and
   Modules.VanishingOnOpen (rank-one section case); neither closes either general hole.
   The two remaining proofs require substantial matrix/sheaf identifications, rather
   than a short application of an existing theorem. Verdict: true and properly split.
4. Read the construction, compactness conversion, both factorization directions, and
   the general pullback/gluing proof from the top down. The latter already uses Mathlib
   locality and adjoint uniqueness and is independently sorry-free. Imports are needed
   for statements or the corresponding proof steps; no proof-only public import was
   introduced. All four old dependencies remain used transitively, so no old node or
   module is pruned. Read sk-prop-av-cube's statement, step, and empty realized fields;
   the determinant reduction remains below the existing node and preserves the route.
   Verdict: pass; no shorter complete route found.
5. Checked all five node records against the Lean declarations and proof steps. The
   parent's proof_deps are the union of its steps' uses; the helper records have their
   required source, searches, creation, blueprint, chapter/unit and Lean fields. Their
   mathematical statements agree with the Lean. Verdict: pass after recording the four
   new primary declaration signatures verbatim, preserving line breaks. The definition record starts at def, as the preflight
   signature parser requires; its Lean declaration remains noncomputable.

Second-reading changes: corrected only those four new nodes' lean.statement formatting
and added this review. No Lean proof or statement needed repair; no further hole closed
or added. Hole accounting remains one original hole closed, two new holes added (net -1).
