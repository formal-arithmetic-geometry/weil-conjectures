## What changed

Reduced AlgebraicGeometry.Scheme.picard_connective_model_comparison to the new
PicardTermwiseModelComparison module, preserving its statement and public imports.
The main module constructs the additive equivalence between single-complex chain
maps and ordinary cycles, conjugates Hom groups by model isomorphisms, and uses
DerivedCategory.connective_single_hom_bijective for localization. It proves
naturality by recovering the unique chain-map representative of a restricted
section and reading its degree-zero component.

The new theorem separates the termwise object computation and canonical
restriction coherence. It assumes strict perfectness but no connectivity and
only handles derived morphisms that are already localized chain maps. Its two
abbreviations are actual termwise functor and single-complex constructions, with
no unproved witness chosen to supply their data.

Both modules compile locally. Repaired the earlier draft's missing Mathlib
additive-adjunction import, iso notation parentheses, and localization universe
inference. The final localized Hom equivalence supplies its derived-category
instance explicitly. The main theorem uses local elaboration settings for
termwise sheaf-functor comparisons; the wall-clock limit is unchanged. Sources consulted:
[06YJ](https://stacks.math.columbia.edu/tag/06YJ),
[0D5S](https://stacks.math.columbia.edu/tag/0D5S), and
[08DW](https://stacks.math.columbia.edu/tag/08DW). Mathlib searches confirm the
single-complex constructor and additive-adjunction ingredients; the prior
LeanFinder search found no complete canonical model comparison.

## Proved and sorry left

Closed the original hole
AlgebraicGeometry.Scheme.picard_connective_model_comparison
(lem-sc-picard-connective-model-comparison) by a complete reduction.
No sorry remains in the original module or its private helpers.

Added one strictly lower hole:
AlgebraicGeometry.Scheme.picard_termwise_model_comparison
(lem-sc-picard-termwise-model-comparison). Its proof is exactly := by sorry.
The theorem computes objects and restriction of given chain maps, leaving the
connective localization and cycle identification to the original module's proof.
This is a decomposition: one hole closed and one added, net zero. It is not a
claim that the original theorem's complete axiom closure is sorry-free.

## No longer needed

Removed the original module's direct proof imports
Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback and
Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf. Their nodes
lem-pc-flat-complex-derived-pullback and
lem-sc-derived-pullback-structure-sheaf-local remain needed by the new termwise
comparison and are not pruned from the targets' closure. The composition node
lem-pc-ringed-spaces-derived-pullback-composition likewise remains needed below
that theorem. ConnectiveSingleHom and all original public imports remain needed.
No node or module is claimed as globally pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked by absent shared compiled dependencies. Both
PicardOrdinaryModelCycles and ConnectiveSingleHom are now available; that
blocker has cleared. The draft itself had never been typechecked, and required
the concrete elaboration repairs described above.

No mathematical dispute or signature correction was needed. The original
pointwise object-comparison lemmas do not themselves give the simultaneous
canonical restriction equation, so that coherence remains explicit in the new
node rather than being silently assumed. The unit sk-prop-av-cube has empty
realized statement and step lists; no unit or chapter route is changed.

## New nodes

lem-sc-picard-termwise-model-comparison: source and target object comparisons,
and compatibility of restriction on localized chain maps, without negative-term
vanishing. It carries original plan steps 1 and 3; step 2 and the inverse
localization/naturality glue are proved in the original module. The node records
its source, proof in words, dependencies, searches, ancestry, and Lean statement.
Zero complexes, empty opens, and empty test schemes remain valid because the
additive functors preserve zero objects. Positive and negative model terms are
allowed in this theorem; negative vanishing enters only in the main proof.
No change records or forced adaptations are needed.

## Second reading by M3

1. I compared the delivered main module against the repository version. The target
   theorem signature is unchanged; the new termwise module and its theorem are the
   only added declarations, and the report records the added split node.
2. Both delivered Lean modules compile with `lcompile.py --all`. The main theorem
   closes its original `sorry`; the only remaining `sorry` is the named lower
   theorem `picard_termwise_model_comparison`, with its source proof and DAG node.
   No forbidden declarations or hollow definitions occur.
3. The split statement is a genuine lower-level object-and-restriction computation,
   strictly weaker than the connective target because it assumes a chain map and
   makes no connectivity claim. Its abbreviations construct the termwise objects
   explicitly. The edge cases of zero complexes and empty opens are preserved by
   the additive functors.
4. The proof uses the shortest available declared comparisons and the single-complex
   cycle equivalence; removed direct pullback imports are no longer needed in the
   main module and remain available to the lower module. No additional library
   declaration duplicates an existing one.
5. The unit `sk-prop-av-cube` has no realized statement or proof steps, so its route
   is unchanged. The new node records the lower proof dependencies and the report's
   pruning list agrees with the imports.

I changed only the report by adding this second-reading record; no Lean statement,
definition, or proof was altered during review.
