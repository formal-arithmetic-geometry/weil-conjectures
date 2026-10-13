## What changed

In `Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder`, completed
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_left_homology_ladder`
without changing its signature or public imports. Added proof imports of
`Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes`,
`Sheaf.Algebra.Homology.TensorKunnethNat`, and
`Mathlib.Algebra.Homology.HomologySequenceLemmas`.

The private, completely proved helper `normalized_homology_eq` shows that any two
normalized external-cup cochain maps induce the same homology map. It uses tensor
Kunneth, lifts factor classes via the epi homology projections, and checks equality
on pure tensors in each direct-sum component. The second proved private helper
`isIso_of_comparison_square` transfers invertibility through two comparison isomorphisms.

The main proof constructs the rows by deleting the first term of Mathlib's six-term
homology sequence. Its map is the similarly restricted natural homology-sequence
map. Thus the connecting square and all three interior exactness conditions follow
from Mathlib, rather than being included in the remaining hole. The outer arrows
are identified by the comparison squares and normalization uniqueness. At n=0,
the preceding degree is -1; the negative terms give zero homology objects, so maps
between them are invertible without any degree-zero vanishing assumption.

The geometric cochain construction and its scalar-model comparisons are isolated
in the new module `Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes`.
Its input includes no specified cochain maps and no chosen degree; its output is a
morphism of short exact sequences of complexes with degreewise model comparisons.
It asserts no five-term exact rows, connecting squares, or outer invertibility.
The original theorem is assembled from this construction by real Lean proofs.
Both delivered modules compile cleanly with lcompile.py.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_left_homology_ladder`
(node `lem-sc-picard-external-cup-left-homology-ladder`). No sorry remains in the
assigned module. Both private helpers are proved with no sorry.

Added exactly one public theorem with proof `:= by sorry`:
`AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_comparison_complexes`
(node `lem-sc-picard-external-cup-left-comparison-complexes`), in the new module.
Its docstring contains the construction and normalization proof step by step.
This is a decomposition: one original hole closed and one smaller geometric
construction hole added, net zero holes. The entire library is not claimed to be
free of sorry or sorryAx.

## No longer needed

No existing import was removed. The three original public imports are needed by
the unchanged statement. No unused proof import is retained.

The separate planned dependency `lem-sc-cech-comparison-natural` and its module
`Sheaf.AlgebraicGeometry.AffineModuleCechComparisonNatural` are not needed on this
proof route: canonical comparison existence/naturality and affine invertibility
suffice for the construction node. This does not claim the module is unreachable
from every other target branch. The remaining geometric dependencies of the old
plan are needed under the new construction node, not globally pruned:
`lem-sc-cech-comparison-map-iso-affine`,
`lem-sc-cech-comparison-map-naturality`,
`lem-sc-picard-affine-diagonal-intersections`,
`lem-sc-picard-cech-cup-pullback-compat`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-flat-tensor-exact`,
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-qcqs-finite-affine-open-cover`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, and
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`.
`lem-sc-picard-external-cup-cochain` supplies the construction's normalized maps;
it is no longer a direct proof dependency of the assigned node, but remains a
statement dependency. `lem-sc-picard-kunneth-resolution-model` and
`lem-sc-qcoh-cech-total-tensor-nat-iso` remain direct proof dependencies because the
normalization uniqueness helper uses their declarations. The two
long-exact-sequence nodes remain direct proof dependencies of the assigned node,
realized by Mathlib's HomologySequenceLemmas.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The old DAG's geometric
steps describe valid constructions, but their existing declarations do not directly
package a morphism of short exact complexes together with the required model
comparisons. That missing glue is exactly the new node. The old proof-dependency list also
omitted quasi-coherence of pulled-back coefficients: the construction node now
cites `lem-weil-pbc-module-pullback-quasi-coherent` and the adjunction identifying
standard pullback with tensorPullback. It cites the existing refinement and Cech
cup construction nodes explicitly for their cochain formulas and Leibniz identity.
There is no obstacle from
using existing declarations whose own proofs contain sorry.

The local literature checkout has no varieties.tex or unit Markdown; the source
was read on the Stacks Project page https://stacks.math.columbia.edu/tag/0BED,
especially its short exact coefficient diagram after equation the project server.
The unit record `sk-prop-av-cube` was read: its realized arrays are empty; no unit
statement or route was bypassed. Whole-blueprint searches for external cup and
kunneth found no existing blueprint statement for the new construction.
LeanSearch returned Internal Server Error and is recorded as unavailable.
An additional source-library search found `TopCat.Sheaf.shortExact_cechComplex`,
which concerns abelian sheaves and does not package the required k-linear tensor
complex, product coefficient maps, or scalar-model comparisons.
`picard_kunneth_cech_models` imports the quasi-isomorphism theorem whose proof
already depends on this assigned ladder, so it cannot be used here. The scalar-cup
coefficient-naturality and degree-zero Ext-boundary results likewise do not give
the required cochain construction or all-degree connecting squares. No such
unused imports were added.
LeanFinder and source grep found generic homological-algebra results but no
matching geometric construction; all recorded searches were actually run.

Edge cases checked: n=0 uses two negative zero homology objects, and requires no
quotient degree-zero vanishing; positive n uses natural n-1. Empty schemes and
zero coefficients permit zero Cech complexes and satisfy all comparison formulas.
Existential choices in the new theorem are consumed only in the proof; no
arbitrary existence witness is used to define a library object.

## New nodes

`lem-sc-picard-external-cup-left-comparison-complexes` isolates the construction of
short exact Cech comparison complexes and their normalized homology transport
(steps 1-3 of the original plan). It follows Tag 0BED's cochain diagram and the
canonical comparison/cup compatibility declarations. It excludes the long exact
sequence, its connecting square, extraction of a five-term row, and invertibility
transfer, all of which are proved in the assigned module. No change record or
forced adaptation is needed: every existing signature and public import is unchanged.

## Second reading by C4

1. **Interface: pass.** Compared both delivered modules with the repository.
   The comparison module is new; the existing ladder's declaration signature and
   docstring are byte for byte unchanged. The declaration-diff checker reports
   no statement changes. Its three public imports are unchanged. There are no
   public definitions added and no change record is required.
2. **Proof and trust: pass as a decomposition.** Recompiled the two modules in
   import order with lcompile.py (5.0 and 6.7 seconds; no warnings or errors).
   Read every tactic in the normalization, comparison-square, and ladder proofs.
   A scratch copy with explicit #print axioms checks shows only propext,
   Classical.choice, Quot.sound, and sorryAx for the normalization helper and
   ladder, which use open upstream results; the comparison-square helper has
   only the three permitted axioms. The new comparison theorem has sorryAx as
   reported. Exactly that one named public theorem contains sorry; no definition
   contains a hole, no forbidden declaration occurs, and existential witnesses
   are eliminated inside a proof, never chosen as data of a library definition.
3. **Split statement: pass.** Read the construction statement and its complete
   docstring against Stacks Tag 0BED, equation the project server and the following short
   exact coefficient diagram. Affine sections and field tensor give the two
   short exact complex rows, and refinement/cup compatibility gives their map.
   The scalar and tensor Kunneth comparisons give precisely the asserted
   homology squares. The result isolates the cochain construction: it does not
   assert the five-term exact ladder, connecting square, or outer invertibility.
   It is a strict part of the original argument, not its restatement. Checked
   zero coefficients, empty schemes, natural degree zero, and negative support.
   Repeated LeanFinder searches using “Functorial tensor total Cech complex
   comparison” and “Naturality of connecting homomorphisms”; found the Mathlib
   homology-sequence naturality already used here, and generic Mayer-Vietoris
   results, not this geometric construction. Independent source searches for
   coefficient naturality, comparison complexes, and shortExact_cechComplex
   found no matching theorem. Read the existing affine comparison, pullback/cup
   compatibility, and tensor Kunneth declarations; none packages this construction.
   The remaining construction cannot be closed by a few-minute application of
   those declarations.
4. **Route and pruning: pass.** The proof uses Mathlib's exact homology sequences
   directly. Deleting their first term gives the required five-term rows; their
   mapped sequence supplies all commuting squares. Normalization uniqueness
   identifies the specified cup maps, and comparison-square conjugation transfers
   the four isomorphisms. At n=0 the preceding degree is -1, where zero terms
   imply zero homology. Every original proof dependency removed from the direct
   list is accounted for above: retained beneath the construction, retained as a
   statement dependency, or the unused cech-comparison-natural route. No module
   import is removed and no whole module is claimed pruned. The unit
   sk-prop-av-cube has empty realized arrays; its statement and route are unchanged.
5. **DAG: pass.** The existing node changes only proof, proof_deps, proof_origin.
   Both nodes' proof_deps equal the union of their steps' uses. The new node has
   the source, self-contained statement, construction proof, search records,
   blueprint ancestry, creation record, and verbatim Lean signature. Its single
   hole and the closed original hole are both accurately named above: one closed,
   one added, net zero; this is a decomposition rather than a net hole reduction.

Second reading changed only this review report. No mathematical repair was needed.
