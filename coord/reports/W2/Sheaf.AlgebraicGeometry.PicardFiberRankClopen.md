## What changed

Proved `AlgebraicGeometry.Scheme.picardFiberRank_clopen` in
`Sheaf.AlgebraicGeometry.PicardFiberRankClopen`, with its signature and all original
public imports unchanged. Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank`,
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank`,
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.

The proof constructs the local fixed-rank locus from actual neighbourhoods. On overlaps,
the existing proved stalk-finrank theorem identifies the two ranks. This makes the locus
clopen. Restriction/pullback compatibility, fixed-rank pullback preservation, and locality
show that any tensor pullback has rank r exactly when every point maps into this locus.
The fibre loci are then the complements of the image of the bad-rank locus and of range f.
Flat local finite presentation makes these images open; properness makes them closed.
All private helpers are proved, and both private definitions are explicit constructions.
The tensor/ordinary pullback comparison uses uniqueness of left adjoints, which determines
the comparison isomorphism; no arbitrary data is chosen from an unproved existence result.

Updated only proof, proof_deps and proof_origin of
`lem-sc-picard-fiber-rank-clopen` to record the compiled argument and its stalk-finrank
input. The unit record has no realized statement or steps for this item, and its route
remains unchanged. No public interfaces or other modules were adapted.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.picardFiberRank_clopen`
(node `lem-sc-picard-fiber-rank-clopen`).
No sorries remain in the item, and no holes or modules were added.
This is a proof, not a decomposition.

The file compiles with lcompile.py, and `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The proof does not assume a nonempty scheme or fibre,
positive rank, connected fibres, surjectivity, or finitely many global ranks. The
pullback criterion uses an empty cover on an empty source, so every rank is admitted on
empty fibres. A nonempty mixed-rank fibre fails the criterion because every fibre point
must map into the same rank locus. Zero-rank frames are allowed throughout.

## No longer needed

Removed the first worker’s redundant proof-only import
`Mathlib.AlgebraicGeometry.PullbackCarrier`: its declarations are already available
through the retained imports. No original imports, old proof-dependency nodes, or
modules in the target closure are pruned. All six original public imports remain
needed for statements or their types. Each remaining added proof import is necessary:
fixed-rank pullback and local gluing, uniqueness of ranks at a point, and openness of f.
The proof avoids constructing a global stalk-rank function or a separate general theorem
on ranks under residue-field extension; no extra nodes for these are needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface mismatch found. The original DAG cited definitions for
its substantive rank argument; the delivery supplies that argument in private proved
helpers and adds the existing stalk-finrank node as an explicit dependency.
The cited source, Stacks Tag 0BDP, first proof paragraph, was read. Its connected-fibre
hypothesis is used there for a disjoint base rank decomposition. This item instead uses
the complement of the image of the bad-rank locus, as its existing statement and proof
plan require, so overlapping images of different rank loci cause no problem.
Searches through msearch.py (LeanFinder, Loogle and grep) and rg found the existing
fixed-rank pullback/locality and stalk-finrank results used here; no exact fibre-locus
theorem was found.

## Second reading by W2

1. **Interface preservation — pass.** Diffed the sole delivered module against the
   repository and compared the existing theorem signature byte for byte. Its
   hypotheses, conclusion, universes, visibility and docstring are unchanged.
   The six original public imports are unchanged; new helpers are private and new
   imports are proof-only. No change records or adapted modules are required.
2. **Proof and axioms — pass.** Independently compiled the complete module without
   errors or warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.picardFiberRank_clopen` reports only `propext`,
   `Classical.choice`, and `Quot.sound`. Scanned for sorry and forbidden declarations;
   none occur. Both private definitions are explicit constructions. The comparison
   of tensor and ordinary pullback is an isomorphism determined by adjoint uniqueness;
   it introduces no arbitrary object from a holed existence theorem.
3. **Split statements and edge cases — pass.** There are no split-off statements,
   new holes or new nodes. Read each private helper: rank uniqueness requires a point,
   so it cannot assert equal ranks on an empty scheme. The pullback converse uses a
   cover indexed by all source points, including the empty cover. Rank zero is allowed
   by `Fin 0`; mixed-rank fibres meet the bad-rank locus and fail the fixed-rank condition.
   Repeated LeanFinder and Loogle searches with different wording and searched scheme
   modules using rg. Existing fixed-rank pullback, locality and stalk-finrank results
   are used; no shorter exact scheme-fibre theorem was found.
4. **Route and pruning — pass after repair.** Read from the complement-of-image
   conclusion down through pullback compatibility and local rank uniqueness. Checked
   the source's first paragraph at https://stacks.math.columbia.edu/tag/0BDP:
   its connectedness assumption is unnecessary for this complement-of-bad-image
   argument. The unit `sk-prop-av-cube` has empty realized statement/step lists and
   is unchanged. Every original proof dependency is retained. Tested omission of each
   added import in scratch copies: omission of LocallyFreeRank, StalkFinrank or
   UniversallyOpen fails; omission of PullbackCarrier compiles. Removed PullbackCarrier.
5. **DAG agreement — pass.** Diffed the node: only `proof`, `proof_deps` and
   `proof_origin` change. Checked that `proof_deps` is exactly the union of step uses,
   including the existing stalk-finrank node. The four proof steps describe the actual
   local-frame, pullback, fibre-range and clopen-image argument. No node statement or
   unit route changes.

Changed only the redundant PullbackCarrier import and this report; retained the
mathematically correct proof and node update. Independently confirmed one original
hole closed, zero holes added, and zero split-off statements.
