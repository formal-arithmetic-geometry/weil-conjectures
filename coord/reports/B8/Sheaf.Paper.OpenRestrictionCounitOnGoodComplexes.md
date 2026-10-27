## What changed

Replaced the proof hole in
`WeilConjectures.CanonicalOpenRestriction.openRestrictionCounitOnGoodComplexes`
without changing its statement or its public imports. Three new modules supply
proved general steps: strict assembly of maps between quotient presentations,
naturality of augmented presentations, and evaluation of the transported ordinary
system counit. The item uses these as private proof imports. Its node now records
this route. No other existing module or node is changed.

The extension and restriction hypotheses can choose different strict models for
the same restricted integral complex. The proof compares them explicitly using
strict assembly applied to the integral identity. It also assembles the integral
ordinary counit and identifies both resulting derived maps through the strict
augmentations. The finite computation is ordinary adjunction naturality and the
triangle identity; equality is checked by ordinary system evaluation before
localization. The ordinary assembly is proved for an arbitrary ringed sequence
site and then specialized to the coefficient rings; the public generic
continuity instance is its only additional proof import.

## Proved and sorry left

One original hole is closed:
`WeilConjectures.CanonicalOpenRestriction.openRestrictionCounitOnGoodComplexes`
(node `lem-sf-open-restriction-counit-on-good-complexes`).

The new public theorems are
`WeilConjectures.CanonicalOpenRestriction.strictReductionPresentationMap`,
`WeilConjectures.CanonicalOpenRestriction.augmentedReductionNaturality`, and
`WeilConjectures.CanonicalOpenRestriction.openSystemCounitEvaluation`.
They contain complete proofs. Holes added: zero. Holes remaining in the delivered
modules: zero. The delivery uses existing coefficient-calculus declarations as
permitted by the stage-3 dependency policy.

Validation: `lcompile.py --all` passed for all four delivered Lean modules,
with no compiler errors or warnings. The original item signature was compared
verbatim with the current repository source and is unchanged.

## No longer needed

No existing public import is removed and no module is withdrawn.
The original node's separate proof dependencies on
`lem-coef-semilinear-derived-sections`, `lem-sf-open-tensor-normalization`, and
`def-weil-pbc-adjunction-mate` are not used as proof lemmas: their relevant
structures and definitions remain available through the unchanged statement
import. The new proof uses the ordinary counit evaluation equation already
recorded by `Operations.openSystems` and the exact-adjunction localization API.
The generator-normalization argument planned for tensor is unnecessary because
`hs` already supplies the entire finite unit/inverse-tensor/counit equation, and
`hr` supplies the matching tensor equation. Naturality and the triangle identity
combine those equations directly. This prunes proof obligations in the old plan,
not existing declarations or statement dependencies.

## Where the brief, the DAG or earlier work was wrong

The original plan does not explicitly reconcile the independent strict models
chosen by `hr` and `hs`. Finite agreement alone would not identify arbitrary
morphisms in the derived category. The proof constructs an ordinary strict map
between these models and uses the augmentation normalization under the two
adjunctions to identify its localization. Derived finite evaluation is never used
as a faithful functor.

The tensor generator step in the old plan is redundant for the hypotheses of
this theorem: the required finite map formulas are already assumed. No statement
repair, shared-definition change, or forced adaptation is made.

## New nodes

`lem-sf-strict-reduction-presentation-map` records construction of a strict
chain-system map from an integral chain map and two horizontally compatible
quotient presentations. It contains no open immersion or derived counit.

`lem-sf-augmented-reduction-naturality` records that such a strict map computes
reduction of the integral map when the two presentations satisfy the actual
scalar-unit augmentation condition. It is an equality under the reduction/limit
and constant-tower adjunctions, independent of open operations.

`lem-sf-open-system-counit-evaluation` records the ordinary finite evaluation of
the transported system counit. It uses the equivalence triangle law and the
specified ordinary open-system evaluation equation, without chain complexes or
derived localization.

No change record is required: all existing interfaces are unchanged.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
