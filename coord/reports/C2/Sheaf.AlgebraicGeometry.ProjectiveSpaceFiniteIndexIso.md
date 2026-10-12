## What changed

Replaced the sorry in `AlgebraicGeometry.ProjectiveSpace.exists_finite_index_iso`
without changing its signature or its public imports. The proof chooses a positive
cardinality, reorders the coordinate sections, and uses the native
`homOfIsFreeGenerator` construction. Its base-map equality and twisting-module
comparison are proved by `homOfIsFreeGenerator_over`, `twistRestrictHom`, and
`Scheme.Modules.pullbackId`.

One new module, `Sheaf.AlgebraicGeometry.ProjectiveSpaceReindexIsIso`, isolates only
the invertibility of this specific constructed scheme morphism. It does not assert
a cardinality choice, an over-base equality, or a twisting-module comparison.
The main module imports it privately. Both modules compile with lcompile.py.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProjectiveSpace.exists_finite_index_iso`
(node `lem-weil-pbc-projective-space-finite-index-iso`). No sorry remains in the item.

Added one hole:
`AlgebraicGeometry.ProjectiveSpace.isIso_homOfIsFreeGenerator_reindex`
(node `lem-weil-pbc-projective-space-reindex-is-iso`). Its proof is exactly `by sorry`;
its docstring gives the coordinate-chart argument and inverse construction.
This is a decomposition: one upper hole closed, one strictly smaller geometric
obligation added, net zero holes. The finite-cardinality argument and O(1)
comparison are complete Lean proofs.

Edge cases checked: a singleton coordinate type gives n = 0; the cardinality
argument cannot select n from an empty type because the original theorem assumes
Nonempty. The new isomorphism lemma also covers empty coordinate types, when both
projective spaces have an empty standard-open cover. An empty base scheme causes
no problem. No hypothesis about affineness or the characteristic is introduced.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.TensorPullback` and
`Sheaf.Topology.GlueSheavesOfModules`. The native categorical module pullback and
the native twistRestrictHom construction supply all needed module operations.

The parent proof no longer needs node `lem-weil-pbc-glue-sheaves-of-modules`
or its module `Sheaf.Topology.GlueSheavesOfModules`, and does not need the custom
tensor-pullback implementation in `Sheaf.AlgebraicGeometry.TensorPullback`.
Native proved constructions perform the module gluing. These are local pruning
claims; other targets may still reach these modules independently.
The scheme-morphism-gluing node `lem-weil-pbc-scheme-morphism-gluing` is a Mathlib
leaf, and remains in the route: it is implemented by the native gluing construction.
The definition nodes def-pc-proj, def-pc-module-pullback and
def-pc-projective-space-twist remain needed. No unit-realizing node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan overlooks the already proved native `ProjectiveSpace.OfInvertible`
construction, which gives both the over-base morphism and the O(1) comparison.
Only its invertibility under coordinate reindexing still needs proof. A generic
scheme isomorphism over the base would not suffice for the O(1) comparison; the
remaining lemma deliberately concerns this particular coordinate map.

The cited local literature file is absent on this machine; the source statements
were read at https://stacks.math.columbia.edu/tag/01NE and
https://stacks.math.columbia.edu/tag/01NF. LeanSearch was unavailable; Loogle,
LeanFinder, and local source searches were used. No statement correction is needed.

## New nodes

`lem-weil-pbc-projective-space-reindex-is-iso` states invertibility of the morphism
constructed from reordered coordinate sections. It is sourced to Stacks Tags 01NE
and 01NF, with the complete chartwise inverse proof in its docstring and node.
The native scheme and twist definitions are its dependencies. Searches found
ring-level rename equivalences, affine reindexing, and native coordinate-chart
computations, but no theorem asserting invertibility of this specific morphism.
No change record is needed: no existing signature, definition, public import,
namespace opening, or target statement changed.

## Second reading by C2

1. Compared the item with the repository using diff. The existing declaration's
   signature is byte for byte unchanged, and its public Twist import is unchanged.
   Only its proof, proof docstring, and private proof imports differ. The new
   module adds a theorem, with no definition or change to an existing interface.
   Verdict: unchanged meaning; no change record required.
2. Compiled both delivered modules in import order with lcompile.py. Scratch
   copies with #print axioms for both declarations compile and show only propext,
   Classical.choice, Quot.sound and sorryAx. The sole sorry is exactly the named
   isIso_homOfIsFreeGenerator_reindex theorem reported above. No forbidden
   declaration, hidden hole, or data chosen from arbitrary unproved existence is
   present: phi is constructed, and asIso uses a uniquely determined inverse.
   Verdict: valid reduction with one remaining proof obligation.
3. Read the native OfInvertible construction, standardOpenIso, and the cited
   Stacks Tags 01NE and 01NF. The reindexing theorem is true, needs no finite-type
   hypothesis, and isolates only invertibility of the explicit coordinate map.
   Singleton coordinates give n = 0; empty coordinate types have the empty
   standard cover; infinite coordinate types still have polynomial charts and
   finite-support polynomials; an empty or nonaffine base introduces no exception.
   New searches used Loogle for homOfIsFreeGenerator, LeanFinder for locality of
   scheme isomorphisms, and rg for chart extensionality and affine reindexing in
   Mathlib, upstream, and lean/Sheaf. No duplicate or immediate closing lemma was
   found. Verdict: strictly smaller geometric obligation, not a restatement of
   the parent, with a complete chartwise proof in words.
4. Checked the proof from the target down: the cardinality choice and module
   comparison use native proved constructions; OfInvertible contains no sorry.
   The public imports are needed by the signatures; the private new import is
   used by the proof. Compared the old proof_deps with the new set: the only
   removed node is lem-weil-pbc-glue-sheaves-of-modules, already reported, and
   both removed modules are listed under No longer needed. Checked
   dag/units/sk-thm-p1.json realized: no realizing node is bypassed or changed.
   Verdict: pruning and unit route are correct; net zero holes, a decomposition.
5. Compared both node records with their Lean declarations and proof route.
   proof_deps equals the union of the step uses. The new node has its source,
   complete proof, searches, creation, blueprint, chapter, unit, and exact Lean
   statement. The parent changes only proof, proof_deps and proof_origin.
   Verdict: nodes agree with the implementation and remaining obligation.

Changed the split-off theorem's proof docstring and its matching DAG proof to
make the nonaffine-base argument explicit: use standardOpenIso for relative
charts, restrict to an affine cover Spec R of S, and note that the coordinate
ring maps fix R by homOfIsFreeGenerator_over. Added the independent search
results to the new node. No Lean proof or statement needed repair. This delivery
closes one original syntactic hole and adds one lower hole; it does not claim a
sorry-free proof of the parent.
