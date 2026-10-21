## What changed

Completed the body of `WeilConjectures.RamifiedPullback.identification` without changing its signature or any field of `Identification`. The proof constructs the unique positive ramification exponent using DVR factorization, constructs the actual quotient maps by `Ideal.Quotient.lift`, proves their normalization, obtains the two coefficient comparisons and the finite pullback comparison, and constructs `sameIndex` by composing the ramified comparison with the actual tower reduction. The same-index tensor formula follows by reducing both quotient coefficients and using the limit projection identity. Factorization is definitional.

Moved every pre-existing definition and both structures verbatim to `Sheaf.Paper.RamifiedPullbackTowerData`, publicly re-exported by the item module. This gives the two separate comparison lemmas access to the existing interfaces without an import cycle. It changes no definition, public declaration signature, coefficient universe, or target statement. The module-level variable declarations and instance settings are retained. No source-library module was edited.

Added the fully proved `Sheaf.Paper.FinitePullbackTransitionGenerators`: its adjacent case uses the actual defining pullback transition equation, the finite reduction equation, surjectivity of the completed projection, and completed linearity. Induction and the tower functor laws give the formula for every pair of indices.

Separated the source argument into coefficient quotient comparison (`RamifiedCoefficientQuotientComparison`) and normalized finite pullback base change (`RamifiedFinitePullbackComparison`). Each contains a public statement with its own source, proof in words and DAG node. Neither is a renamed copy of the original theorem: the first concerns a single scheme and coefficient modules, while the second assumes those coefficient data and concerns only finite pullback. The original theorem supplies the arithmetic, quotient construction and same-index factorization itself.

Validation: all five delivery modules have been compiled individually through `lcompile.py`. A final dependency-ordered sandbox compilation checks their current versions. The only successful-compilation warning, a redundant `change`, was removed. Busy-server timeouts were retried. The temporary ordinary tensor quotient investigation is not part of the delivery.

## Proved and sorry left

This is a decomposition, not a net reduction of proof holes: one existing hole is closed and two strictly smaller holes are added.

Closed: `WeilConjectures.RamifiedPullback.identification` (the item's original and only hole). Its body is complete Lean, including ramification uniqueness, quotient maps, and same-index construction and formula.

Proved without adding a hole: `WeilConjectures.RamifiedPullback.pullTensor_transition`, node `lem-weil-finite-pullback-transition-generators`; all private arithmetic, quotient reduction and projection lemmas are also proved.

Added and still `sorry`:

- `WeilConjectures.RamifiedPullback.coefficients_exists`, node `lem-weil-ramified-coefficient-quotient-comparison`: coefficient quotient scalar extension, normalized on tensors and compatible with finite reductions.
- `WeilConjectures.RamifiedPullback.finitePullbackComparison_exists`, node `lem-weil-ramified-finite-pullback-comparison`: finite pullback base change from the supplied coefficient data, with its tensor formula and adjacent tower square.

There are zero `sorry`s in the item module and in the shared data and transition modules. Each of the two remaining holes is exactly a named public theorem body `:= by sorry`. There are no new axioms, private holes, or data definitions with holes.

## No longer needed

Removed the item's direct proof imports `Sheaf.Paper.ConstantCompletionEquivalence`, `Sheaf.Paper.RingedTopoiTensorSections`, and `Sheaf.Paper.RingedTopoiInverseImageTensorComparison`. They are not used by the completed parent proof; their relevant arguments remain in the two smaller comparison nodes' proof plans. Consequently this delivery does not claim those modules or their nodes as globally pruned.

The parent no longer needs the source argument's generic tensor or inverse-image constructions directly. It uses the two explicitly normalized subresults instead, plus the finite pullback generator transition lemma. The DAG proof dependencies are updated accordingly. No module is withdrawn, no adopted source declaration is removed, and no unit statement or realized unit step is bypassed. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

No target or planned mathematical statement was found false. The original one-module interface could not be imported by separate comparison statements without a cycle; extracting its unchanged definitions resolves that interface issue. The existing generic completion and inverse-image statements are not immediate exact matches for these independently sized, normalized coefficient towers, so two explicit specializations remain separate results rather than being asserted as automatic applications. The edge cases used here include equal transition indices, exponent one, arbitrary positive ramification, and arbitrary (not bounded or flat) input complexes. Arithmetic positivity is proved before natural-number subtraction is used to recover the exponent.

## New nodes

`def-weil-ramified-pullback-tower-data`: records the unchanged coefficient and tower interfaces in their new common module. Its declarations are the original definitions and structures, moved verbatim. Change record: `coord/changes/ramified-pullback-tower-data.md`. Consumer checks for both `Coefficients` and `Identification` found no other current Lean module using them; the item continues to re-export every declaration.

`lem-weil-ramified-coefficient-quotient-comparison`: the coefficient part of source steps 2–4, assuming the ramification exponent and explicitly normalized quotient maps, on one scheme. It leaves one named theorem hole.

`lem-weil-ramified-finite-pullback-comparison`: source steps 5–7, assuming the coefficient data on the source and target schemes and providing the normalized finite pullback isomorphisms and their tower square. It leaves one named theorem hole.

`lem-weil-finite-pullback-transition-generators`: the fully proved formula for an arbitrary composite of actual finite pullback transitions on pure tensor generators. Its proof uses the defining adjacent transition and induction, not an assumed replacement tower.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
