## What changed

Constructed the ordinary part of the native Frobenius model from actual coefficient functions
and explicit slice maps. The original structure and theorem signature are unchanged.

`Sheaf.CategoryTheory.SmallSiteModuleHom` constructs the AsSmall module restriction
equivalence, proves additivity, and constructs the pointwise internal Hom comparison by
lifting and unlifting slice arrows. Its inverse equations, linearity, restriction naturality
and two-variable Hom naturality are proved.

`Sheaf.CategoryTheory.HomComparisonEquivalence` proves the abstract reversal of a Hom
comparison along an equivalence, and the composition of two component naturality squares.

`Sheaf.SixFunctors.NativeHomBifunctorComparison` packages the proved normalized native Hom
comparison in its two variables and reverses it along the native section equivalence.

`Sheaf.Paper.NativeFrobeniusModelData` restricts the actual comparisonRing, proves continuity
of translation in both directions, and identifies coefficients by the identity on functions.
Its additive equivalence has forward functor equal to small-site restriction followed by the
inverse native section equivalence.

`Sheaf.Paper.NativeFrobeniusHomComparison` composes the proved small-site Hom isomorphism
with the reversed normalized native Hom comparison. `Sheaf.Paper.NativeFrobeniusHomNaturality`
proves its naturality by composing their two naturality squares. These give the pointwise
results the target needs. The three modules separate the costly definitions and naturality
proof after simplifying the equivalence forward functor and limiting reducibility locally;
the combined file exceeded the 60-second compile limit.

`Sheaf.Paper.NativeFrobeniusComparison` isolates the remaining native inverse-pushforward
comparison and its Hom square for these specified ordinary data. It chooses no site, ring,
module equivalence or ordinary Hom comparison. The original module assembles the model and
uses the proved pointwise Hom naturality.

Validation: `lcompile.py --all` compiled all eight delivered modules. The ordinary data took
33.8 seconds, native Hom bifunctor 50.1 seconds, pointwise comparison 46.9 seconds,
naturality 51.7 seconds, residual comparison 34.7 seconds and original model 41.6 seconds;
every file met the 60-second limit. No debugging options remain.

## Proved and sorry left

New proved components include `SheafOfModules.SmallSite.equivalence`, `homIso`,
`homIso_naturality`, and `equivalence_functor`; and
`CategoryTheory.HomComparison.inverseHomComparison` and `mapIso_comp_naturality`.
In `AlgebraicGeometry.ProEtale.NativeFrobenius`, the new proved constructions include
`equivalence_additive`, `translation_continuous`, `ringIso`, `forwardHomComparison`,
`inverseNativeHomComparison`, `homComparison`, and `homComparison_naturality`.

Closed the original hole in
`AlgebraicGeometry.ProEtaleWeilSheaf.native_frobenius_ringed_model`, node
`lem-sf-native-frobenius-ringed-model`, by a complete proof from the constructed data and
one remaining comparison.

Added one hole:
`AlgebraicGeometry.ProEtale.NativeFrobenius.nativeFrobeniusComparison`, node
`lem-sf-native-frobenius-comparison`. Its entire proof is `by sorry`; its docstring and node
give the pullback identification, scalar-action calculation and slice evaluation argument.
There are no other holes in the delivered files and no holes inside definitions.

This is a decomposition: one old hole closed, one strictly lower hole added, net zero.
The ordinary site, coefficient ring, additive equivalence and natural Hom comparison are
constructed without new holes. The residual theorem supplies only Frobenius compatibility
for those fixed constructions.

## No longer needed

No existing public import is removed and no existing module is withdrawn or claimed pruned.
A full comparison of the small-site Hom bifunctors is unnecessary: the target record needs
pointwise Hom isomorphisms and their naturality, supplied directly by the slice construction.
The helper modules omit redundant direct CoverLifting imports.

The existence and derived-resolution assertions of `frobenius_action_resolutions` are unused.
Its explicit Site, topology, postcompose and translation constructors are used, so its module
and node stay. The four original dependency modules remain used directly or transitively.

## Where the brief, the DAG or earlier work was wrong

The action-resolution theorem has finite-type, separation and characteristic hypotheses absent
from this item and uses a different coefficient encoding. Its exported site constructors are
general enough; the actual comparisonRing and proved native section equivalence supply the
ordinary coefficient model. Its private continuity proof is not exported, so continuity is
proved for the retained constructors here.

The unit record sk-prop-sf-biduality-general has empty realized statement/step lists. This
change keeps the ordinary Frobenius/internal-Hom route and changes no unit or target statement.

## New nodes

`lem-sf-hom-comparison-equivalence`: proved reversal of Hom comparisons and composition of
component naturality squares, in `Sheaf.CategoryTheory.HomComparisonEquivalence`.

`lem-sf-small-site-module-hom`: proved AsSmall module equivalence and normalized slice Hom,
in `Sheaf.CategoryTheory.SmallSiteModuleHom`.

`lem-sf-native-section-hom-bifunctor`: forward and inverse normalized native Hom bifunctor
comparisons, in `Sheaf.SixFunctors.NativeHomBifunctorComparison`.

`def-sf-native-frobenius-model-data`: explicit coefficient ring, additive ordinary equivalence,
continuity and coefficient identification, in `Sheaf.Paper.NativeFrobeniusModelData`.

`def-sf-native-frobenius-hom-comparison`: the constructed pointwise Hom isomorphism,
in `Sheaf.Paper.NativeFrobeniusHomComparison`.

`lem-sf-native-frobenius-hom-naturality`: its proved two-variable naturality,
in `Sheaf.Paper.NativeFrobeniusHomNaturality`.

`lem-sf-native-frobenius-comparison`: remaining inverse-pushforward compatibility for the
specified data, in `Sheaf.Paper.NativeFrobeniusComparison`.

No existing definition or statement changes; no change record or consumer adaptation is needed.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
