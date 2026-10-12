## What changed

Proved `AlgebraicGeometry.isFinite_of_fpqc_cover` without changing its signature.
Replaced the two proof imports of unfinished Sheaf modules by
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`. The source library already proves
single-morphism finite descent and covering-family descent; their specialization closes
this item. Converted the precoverage hypothesis to a covering sieve and supplied the
canonical pullback squares explicitly. Updated the theorem's proof documentation and
its node's proof, proof_deps and proof_origin to record this route.

## Proved and sorry left

Proved `AlgebraicGeometry.isFinite_of_fpqc_cover` (node
`lem-weil-pbc-fpqc-descend-finite`), the sole original sorry. No sorry remains in the
item and no new theorem, module, sorry, or axiom was added. Local compilation passed.
The delivery dry run also checks the transitive axioms and compiles on the server.
The arbitrary index universe and empty-family case are preserved; the same precoverage
hypothesis is passed to the covering-sieve theorem without a nonemptiness assumption.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcIntegralDescent`, node
  `lem-weil-pbc-fpqc-descend-integral`.
- `Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover`, node
  `lem-weil-pbc-fpqc-descend-locally-finite-type`.

The original direct proof dependency `lem-weil-pbc-finite-iff-integral-lft` is also
unneeded by this module's proof; its Mathlib import stays because the statement uses
`IsFinite`. Definition dependencies `def-weil-finite-integral-morphism`,
`def-weil-finite-type-morphism`, `def-weil-pbc-fpqc-covering`, and
`def-pc-fibre-product` are no longer proof steps; statement dependencies are unchanged.
No imports beyond these two were removed. The subtrees of the removed Sheaf imports
are unnecessary through this item; they may still be reached through other items.

## Where the brief, the DAG or earlier work was wrong

The node's earlier searches already mentioned the proved source-library route, but
stage 2 chose a reduction through two unfinished Sheaf statements. Reading the current
source declarations confirms that the covering-family theorem accepts the arbitrary
index universe and canonical pullbacks, so that route gives a complete proof now.
LeanFinder and Loogle both confirmed the Mathlib finite/integral/local-finite-type
equivalence; local searches found the shorter source route. No unit statement or
realized unit step is bypassed: this item and its removed dependencies are absent
from `dag/units/sk-thm-p1.json`'s realized statements and steps. The original theorem's
hypotheses and conclusion are unchanged. The new proof uses existing proved library
results; it introduces no new mathematical statement needing a new node.

## Second reading by V2

1. **Visible contract: PASS.** Diffed the sole delivered Lean module against the
   repository version and compared the complete theorem signature byte for byte:
   identical. Only its proof, proof documentation, and two private proof imports
   changed. Public imports, universes, hypotheses, conclusion, and all definitions
   remain unchanged. There are no change records or adapted modules.
2. **Proof and axioms: PASS.** Local single-file compilation succeeded without
   warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.isFinite_of_fpqc_cover` compiled and reported exactly
   `propext`, `Classical.choice`, and `Quot.sound`. The delivered module contains
   no sorry or prohibited declaration/attribute. Read the upstream finite-descent
   proof and covering-family descent proof: the canonical pullback squares have
   the required orientation, and precoverage generation supplies the required
   covering sieve.
3. **Split statements: PASS (none).** No declarations, modules, nodes, or sorries
   were split off. The existing theorem retains arbitrary index universe `v` and
   requires no nonemptiness of the family. Empty covers force an empty base by
   joint surjectivity; the covering-family result already handles this case.
4. **Shortest route and pruning: PASS.** Searched the library by fpqc/finite
   descent and covering-family names, and checked Mathlib's Sites.Fpqc,
   Morphisms.FlatDescent, and Morphisms.LocalFlatDescent. The existing upstream
   finite-descent theorem and generic covering-family theorem give the direct
   proof; no shorter available family theorem was found. Both private proof
   imports supply declarations explicitly used. The two public imports supply
   statement vocabulary. All seven original proof dependencies are accounted
   for in `No longer needed`; the definition dependencies remain statement
   dependencies. Neither this item nor its removed theorem dependencies realizes
   a statement or step in any unit. The finite-morphism definition does realize
   part of `sk-def-conv`, and is retained as a statement dependency, so it is not
   globally pruned. The `sk-thm-p1` realized route is unchanged.
5. **Node agreement: PASS.** Compared the node JSON: only `proof`, `proof_deps`,
   and `proof_origin` differ. The two proof steps name the exact upstream
   declarations and canonical pullback/sieve conversion used in Lean. The empty
   `proof_deps` is their union: no DAG lemma is used in the replacement proof;
   the existing library tools are identified in the proof text and origin.
   Node statement, statement dependencies, unit, source, and Lean record agree
   with the unchanged declaration. No new-node fields need checking.

Second reading changed only this report, adding the independent review and the
clarification that the finite-morphism definition remains needed by statements
and by another unit. No repair to the correct Lean proof or node was necessary.
