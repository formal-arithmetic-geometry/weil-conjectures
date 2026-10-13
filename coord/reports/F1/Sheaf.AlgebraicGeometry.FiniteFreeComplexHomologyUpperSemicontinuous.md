## What changed

Proved `ModuleCat.finiteFreeComplex_homology_upperSemicontinuous` in its existing module,
with its statement and visibility unchanged. The proof realizes all three steps of
`lem-sc-finite-free-complex-homology-upper-semicontinuous`:

1. Choose finite bases of the three adjacent terms, extend those bases to each residue
   field, and identify the matrices of the differentials. Apply the source library's
   proved short-complex homology dimension formula to obtain the additive equality
   `dim H + rank outgoing + rank incoming = c`.
2. Apply the source library's proved `Matrix.le_rank_map_iff`, and identify nonzero
   residue-field determinants with membership in principal opens. All minors form a
   finite family, including the size-zero determinant. Products of determinants give
   the intersections of the two rank loci.
3. For each integer threshold, take the finite union over rank pairs in
   `{0, ..., c}²` satisfying the integer inequality. Prove both inclusions using the
   dimension equality and `omega`. Finite unions of principal opens are open and compact;
   the natural-number sublevels then give upper semicontinuity.

Added proof-only imports of `Mathlib.RingTheory.TensorProduct.Free`,
`WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat`, and
`WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank`. All added helpers are private and
proved. The tensor/scalar-extension equivalence is the construction already proved in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`, generalized privately
from `ModuleCat.{u}` to `ModuleCat.{max u v}`. This is needed to handle the item's module
universe and does not change the source library's interface.

Updated the original node's three proof steps to name the concrete Lean constructions.
The proof retains the original matrix/rank-nullity route and its proof dependencies. The private rank formula implements the original node's first
step; it introduces no new unfinished work. No public declarations or definitions were added.

## Proved and sorry left

Closed the sole hole: `ModuleCat.finiteFreeComplex_homology_upperSemicontinuous`
(node `lem-sc-finite-free-complex-homology-upper-semicontinuous`).
No holes remain, and no holes were added or split off.

Local compilation passes without warnings. `#print axioms` for the public theorem reports
exactly `[propext, Classical.choice, Quot.sound]`, so this is a proof, not a decomposition
through unproved intermediate statements. All private helpers are also checked by the
required delivery axiom probe.

The finite-union argument covers negative and zero integer thresholds, empty minors,
zero-dimensional terms, and the zero ring (whose prime spectrum is empty). In particular,
the cardinality of a chosen finite basis, rather than a finrank comparison over the base
ring, is used for the middle dimension. Thus the proof never assumes the base ring is
nontrivial or a field.

## No longer needed

None. No existing imports, nodes, or modules were removed. Both planned dependencies,
`def-weil-matrix-rank` and `lem-weil-pbc-idempotent-charpoly-rank-nullity`, remain represented
by the matrix criterion and short-complex dimension calculation. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was necessary. Boundedness is stronger than the
calculation needs: only the three adjacent finite free terms enter the proof. Its binder
and the rest of the original theorem signature are preserved.

The source library's `ModuleCat.tensorEquivExtendScalars` fixes the module universe to the
ring universe, so it cannot directly be applied to this item's larger module universe.
The private proved generalization resolves this without changing another group's module.

The local literature text is not present on this machine. Read the authoritative Stacks
page https://stacks.math.columbia.edu/tag/0BDI, especially its final three-term matrix and
minor argument, and followed the already recorded affine specialization. Mathlib searches
were run through `msearch.py` (leanfinder, loogle, grep); no complete existing affine
homology-jump theorem was found. The useful existing results were read directly in the
source library and Mathlib, and are the proof-only imports listed above.

## Second reading by F1

1. **Interface preservation: PASS.** Read the complete original and delivered module and
   their diff. The existing public theorem's signature is byte-for-byte identical,
   including both universes, `CommRing`, boundedness, finite freeness in every degree,
   and all four conclusion clauses. Its docstring and every original public import are
   unchanged. The added declarations are private, and the three new imports are plain
   proof-only imports. There are no other delivered modules or interface changes.

2. **Kernel proof: PASS.** Independently compiled the delivered module with `lcompile.py`
   (5.7 seconds, no warnings). Made a fresh scratch copy of the current delivered file,
   appended `#print axioms` for the public theorem and all seven private declarations,
   and compiled it (6.5 seconds). Every axiom list is exactly `propext`, `Classical.choice`,
   and `Quot.sound`, with no `sorryAx`. Scanned the delivered source for `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, and kernel-check bypasses: none occur.
   The private equivalence explicitly constructs both tensor-product maps and proves
   their inverse laws; it does not select arbitrary data from an unproved existence claim.
   Chosen bases come from the proved finite-free basis API.

3. **Split statements and edge cases: PASS.** No statement was split off and no new hole
   was added. Read every private helper: the rank formula compares the actual fibre
   complex with its adjacent short complex; the minor family is finite even with repeated
   indices. For size zero its determinant is one, while oversized minors vanish. The
   identity `dim H + rank M + rank N = c` bounds both ranks even when a term has rank zero.
   Nonpositive integer thresholds give empty sublevels; thresholds above `c` include the
   whole spectrum. The zero ring has no prime and causes no nontriviality assumption.
   The natural-number thresholds in the final semicontinuity proof match the integer
   sublevels by the cast comparison. No truncated natural subtraction is used.

4. **Shortest route, imports, and unit: PASS.** Repeated library searches with different
   terms, inspected `WeilConjectures.AlgebraicGeometry.Modules.FreeComplex` and the source
   short-complex dimension, matrix-minor, and scalar-extension modules. The existing
   scheme-module semicontinuity theorem does not directly give this module-complex result
   or its finite principal-open description; using it would require extra comparison
   work. The existing scalar-extension equivalence has the smaller module universe,
   so the private proved generalization is justified. Fresh LeanFinder and Loogle
   searches found no direct replacement. Every added import supplies a used construction
   or theorem, and the original imports supply the public statement's notions. Both old
   proof dependencies remain used: `Matrix.rank` directly, and rank-nullity inside the
   proved short-complex dimension formula. `## No longer needed` is complete (none).
   Read `dag/units/sk-prop-av-cube.json`, including its empty `realized` lists: this item
   is a supporting node, not its key statement or step. The cube/perfect-jump-loci route
   and the node's three matrix/rank-nullity/minor steps are preserved. Checked the affine
   three-term matrix argument against [Stacks Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI).

5. **DAG agreement: PASS.** Compared the complete old and new node records. Only the
   three proof-step texts changed; their `uses`, `proof_deps`, document `proof_origin`,
   statement, Lean record, chapter, and unit are unchanged. The updated texts accurately
   name the basis transport, additive dimension identity, minor criterion, product
   construction, and bounded finite union appearing in the Lean proof. The rank-nullity
   dependency is genuinely used transitively by the source short-complex theorem.
   There are no new nodes requiring additional fields.

Second reading changed only this report by adding the independent checks above. No
mathematical, Lean, or DAG repair was necessary. Holes closed: one, by
`ModuleCat.finiteFreeComplex_homology_upperSemicontinuous`; holes added: zero.
