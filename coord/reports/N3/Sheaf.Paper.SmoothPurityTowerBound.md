## What changed

Filled `AlgebraicGeometry.ProEtale.sp_tower_bound` in
`Sheaf.Paper.SmoothPurityTowerBound`. Its signature, both public definitions, and
all public imports stay unchanged. All added helpers are private and proved.

The proof first identifies ordinary evaluations of any two section-normalized
abelian presentations by their recorded section, restriction, and morphism fields.
It derives the normalized ordinary comparison supplied by
`SpTowerCalculus.coordinates_realization`, so no equality between the independently
chosen derived-category instances is assumed. Composing with `Fcomparison` and the
realization counit gives the natural compact-support comparison.

Exact realization, exact open extension, and left t-exact total right derivation
prove preservation of the lower bound. Exact level evaluation commutes with
homology; joint detection of zero strict systems and the presentation equivalence
then detect the input tower's lower bound. The existing
`compactSupport_uniform_tor_bound` supplies finite constructibility and both common
output intervals. The smooth case specializes the existing dimension inequality
after base change. The actual coefficient quotient is killed by `ell^(n+1)` by
ideal membership. Adjunction uniqueness identifies the two finite open-extension
models, and isomorphism invariance transports constructibility and Tor amplitude.

The node's proof, proof dependencies, and proof origin now describe this argument.
The final module compiled through `lcompile.py` with exit code zero in 12.4 seconds,
with no errors or warnings.
The section-coordinate theorem is used as a tool: its identity-on-sections
normalization determines the evaluation comparison. Although its proof is still
an existing hole, no arbitrary object is extracted from mere existence: the
ordinary evaluation functor and the comparison's section maps are fixed. Its
unrelated scalar-coordinate choices are unused. The constant-ring pullback and
constructibility comparison nodes are also tools for changing existing finite
coordinates, not substitutes for the unit's finite uniform-bound argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.sp_tower_bound`
(node `sk-lem-sp-tower-bound`). No direct `sorry` remains in the item. Added zero
holes and zero split-off statements. This proves the item from existing declared
dependencies; in particular the existing section-coordinate theorem is not claimed
as proved by this delivery.

## No longer needed

The proof does not use `Sheaf.Paper.SmoothPurityTowerLevels` or
`Sheaf.Paper.ConstantModelTorAmplitude`; their private imports are removed. The
specific compact-support `Fcomparison` already supplies the needed level
comparison, and the finite uniform theorem already supplies the cohomological
interval as well as the Tor interval. Thus a separate tensor-unit reduction is
unnecessary here. Neither module is withdrawn: other consumers and recorded
statement dependencies may still need them.

The unused private import of `Sheaf.CategoryTheory.SystemDerivedEvaluation` is
also omitted: the proof uses the ordinary strict-system zero-detection lemma
already available through the unchanged public imports and derives its own
homology comparison for the specified presentation.

The redundant private imports of
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and
`Sheaf.Paper.SmoothPurityCoefficientTowers` are removed; they remain publicly
available through the unchanged normalized-tower statement import. No claim is
made that these coefficient definitions are globally unnecessary. No module is
withdrawn and no adopted source declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The original plan's final tensor-unit step is already included in clause (2) of
`compactSupport_uniform_tor_bound`; repeating it would add no content. The
statement allows arbitrary `SpCoefficientTowersAbelian` records, whose
`HasDerivedCategory` fields need not be definitionally identical. The proof
therefore compares ordinary evaluations first and derives that comparison using
the chosen record's derived-category instance. No statement or definition repair
was needed. The unit's finite-level preservation and common-interval route is kept.

Searches used LeanFinder for compact support preserving constructible inverse
systems with uniform Tor amplitude, Loogle for `mapDerivedCategory`, and the
recorded grep search for constructible towers, plus repository searches. They
found generic derived-category tools and no duplicate of the tower theorem.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
