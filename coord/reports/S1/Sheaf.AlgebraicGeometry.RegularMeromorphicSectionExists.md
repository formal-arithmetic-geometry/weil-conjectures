## What changed

Proved `AlgebraicGeometry.exists_regularMeromorphicSection` in the assigned module,
following Stacks Divisors Tag 0EMI and the existing two-step DAG plan. Added the proof-only import
`import all WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
to reuse its existing proved private stalk-generator helper, together with the
local-generator, invertibility-bridge, and linear stalk API available through it. All public imports
and the theorem signature remain unchanged.

Two proved private helpers handle the structure-sheaf stalk equivalence and
linearity of a normalized additive stalk equivalence. The first uses the colimit
comparison argument in `RankOneResidueStalkComponent`. The germ of a free generator
is handled directly by the existing
`AlgebraicGeometry.Scheme.Modules.stalk_generator_bijective` theorem; no copy or
wrapper of that theorem is declared.
No upstream file is changed. Existing file-level commands are unchanged; elaboration
options are scoped to individual declarations. The proof constructs the product-coordinate morphism
on every open, proves linearity and naturality, checks injectivity, and identifies
it with the canonical section map by the existing unique extension theorem.

Updated the item's node proof and proof dependencies to record the stalk normalization
and the localization extension property actually used. The latest blueprint unit
`sk-def-av-ample-degree` and Stacks `divisors.tex` labels `lemma-quasi-coherent-K`
and `lemma-regular-meromorphic-section-exists-noetherian` were read.

## Proved and sorry left

Closed one of one holes: `AlgebraicGeometry.exists_regularMeromorphicSection`
(node `lem-sc-regular-meromorphic-section-exists`). Added zero holes; split off zero
statements. The delivered module contains no `sorry`. Its existing dependency
`AlgebraicGeometry.meromorphicSheaf_generic_product` and existing localization
API theorems remain unfinished in their own modules and are used as stated.

## No longer needed

Both original proof dependencies and every original import are retained. Removed
the returned packet's redundant direct proof imports of
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula` and
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`: the reused helper's
module supplies their APIs. Removed the duplicate private
`AlgebraicGeometry.stalk_generator_bijective` declaration entirely.
The proof uses the normalized product bijections; its separate multiplication
operation and fraction-action compatibility clauses are unnecessary here because
an O_X-linear product-coordinate morphism extends its restriction to O_X uniquely.
No node or module is withdrawn. Properness, the field structure, and the finite
dimension hypothesis are unnecessary for this argument, as in Tag 0EMI; their
binders and public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

Repaired the return at head `61f23f53381`: the previous packet copied the
existing private stalk-generator theorem. Lean's `import all` makes the original
private theorem accessible, so the duplicate was unnecessary and has been removed.
The current shared source still has the original one-hole theorem, and this packet
retains the completed proof on top of that source. No source-library file is changed.

No mathematical error. The Lean generic-product theorem gives additive stalk
equivalences rather than bundled linear equivalences. Their normalization on
ordinary germs suffices to prove linearity, so no dependency interface repair
or new statement is needed. The construction also covers the empty scheme and
empty open sets: all product equalities use function extensionality, and no
generic point or point of X is assumed to exist.

Searches: msearch leanfinder returned basic function-field declarations only;
loogle found `SheafOfModules.unitHomEquiv`; msearch grep found no direct theorem.
Local rg located the proved local-generator and stalk arguments used above.

Validation: the repaired module compiles remotely, including after removing the
redundant direct proof imports. Delivery preflight supplies the axiom and hole audit.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
