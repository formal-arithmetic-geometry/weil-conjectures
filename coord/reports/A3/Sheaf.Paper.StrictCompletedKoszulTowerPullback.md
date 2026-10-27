## What changed

Replaced the proof of
`CategoryTheory.ConstantCompletion.strictCompletedKoszulTowerPullback` by an explicit
assembly of total tensor comparison with the bounded dual Koszul tower comparison.
At each coefficient complex and tower index, the isomorphism is the total tensor
comparison followed by tensoring with the dual-tower isomorphism. Its tower naturality,
chain-map equations, inverse, and naturality in the coefficient complex are checked
before the coaugmentation equation is proved using the two unit normalizations.
The original declaration signature and public import are unchanged.

Added two proof-only imports, `Sheaf.Paper.RingedComplexTensorPullback` and
`Sheaf.Paper.CompletedKoszulDualTowerPullback`, with their nodes. The first is a general
normalized comparison for actual total tensor complexes under arbitrary module
inverse image; its proof uses the existing generic module adjunction, canonical
ordinary tensor comparison, total comparison, and ordinary right-unit normalization.
It returns `TensorPullbackComparison`, packaging the isomorphisms, their two
component naturality equations, and the unit normalization. The tensor functors and
unitors are parameters of this structure, avoiding repeated expansion of localized
monoidal data when its fields are used.
The total comparison and its degree-zero normalization are proved first for abstract
additive closed monoidal categories, in private helpers in the same file, then
specialized once to module sheaves. This avoids repeatedly reducing the concrete
sheaf-module monoidal structures while checking the complex-level construction.
The second isolates the bounded finite free dual Koszul tower, including its unit.
It contains no arbitrary coefficient complex and no tensor totalization with one.

The construction uses no inverse limit or derived localization. Empty generator lists,
zero and repeated sections, and zero rings obey the same comparisons. For the bounded
dual-tower statement with an arbitrary specified ring-complex isomorphism j, rescale
the canonical coordinate comparison by the invertible global section relating j to
the canonical rank-one comparison.

## Proved and sorry left

The original one hole in
`CategoryTheory.ConstantCompletion.strictCompletedKoszulTowerPullback`
(node `lem-sfb-strict-completed-koszul-tower-pullback`) is replaced by a complete
assembly proof.

The new general theorem
`CategoryTheory.ConstantCompletion.ringedComplexTensorPullback`
(node `lem-sfb-ringed-complex-tensor-pullback`) has a proof from existing project APIs.

One new hole remains:
`CategoryTheory.ConstantCompletion.completedKoszulDualTowerPullback`
(node `lem-sfb-completed-koszul-dual-tower-pullback`). Its whole proof is `by sorry`;
its docstring gives the finite subset-coordinate argument, scalar compatibility,
transition compatibility and unit normalization, including the degenerate cases.

Hole accounting: 1 original hole closed syntactically; 1 strictly smaller hole added;
0 holes left in the item module. This is a decomposition, with net hole reduction 0,
not a claim to have completed the finite Koszul calculation. No other holes are added.

Validation: `lcompile.py --all` compiled all three modules without warnings:
3.8 seconds for the finite dual-tower statement, 21.8 seconds for the proved tensor
comparison, and 40.3 seconds for the item. The mandatory `deliver3.py` compile and
preflight also check the delivery. The delivered sources contain no profiling options.

## No longer needed

No original import is removed. The item's only original public import,
`Sheaf.Paper.ConstantCompletionEquivalence`, is required by its statement.
No module is withdrawn, and no adopted source-library declaration is changed.

The item's direct proof dependencies on
`lem-sp-completed-pullback-adjunction`,
`lem-weil-pbc-constant-completion-equivalence`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
are replaced by the two explicit smaller comparison nodes. They remain dependencies
of those smaller arguments, so no transitive pruning of these modules is claimed.
`def-weil-pbc-ringed-koszul-system` remains the source of the tower and unit definitions.

The theorem does not require the generic module adjunction's derived-completion
conclusion or the derived tensor comparison's localization conclusion. The tensor
proof uses their existing ordinary and chain-level helpers. No Noetherian or
ideal-generation hypothesis is introduced.

## Where the brief, the DAG or earlier work was wrong

The proof plan's phrase “canonical tensor pullback” needs its ordinary total-complex
representative and a right-unit equation, not merely the isomorphism in derived
categories. The new normalized complex API and explicit coaugmentation proof make
this distinction precise. No statement is disputed or weakened, and the unit route
is unchanged. The remaining bounded dual comparison is a genuine smaller part of
the finite calculation, rather than the original arbitrary-complex tensor assertion
with a different name.

Searches used LeanFinder, Loogle, Mathlib/project ripgrep and whole-blueprint search.
Mathlib has the single-complex mapping comparison and right-unitor component formula;
the project has the ordinary and total tensor comparisons and unit normalization.
No existing cross-site bounded dual Koszul tower comparison was found. The scalar
Koszul comparison concerns restriction of coefficient rings on a fixed site and
cannot directly identify inverse image between these two arbitrary sites.

## New nodes

`lem-sfb-ringed-complex-tensor-pullback` records the normalized complex tensor API
in `lean/Sheaf/Paper/RingedComplexTensorPullback.lean`. It concerns arbitrary ringed
module inverse image and arbitrary complexes, with no Koszul or completion hypothesis.

`lem-sfb-completed-koszul-dual-tower-pullback` records the bounded finite free dual
Koszul tower comparison in `lean/Sheaf/Paper/CompletedKoszulDualTowerPullback.lean`.
This is the remaining finite calculation from the original plan. It fixes compatibility
with a specified ring-complex comparison and has no arbitrary coefficient complex.

No change record is needed: no existing statement, definition, instance, visibility,
or public import is changed.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
