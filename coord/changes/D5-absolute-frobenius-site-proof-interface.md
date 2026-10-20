# absoluteFrobenius_proEtale_trivialization

## Reason

Close the existing theorem by explicit relative Frobenius, module adjunction and
exact-derived coherence. Record the proof-local reducibility settings conservatively.
In the item, no public declaration signature, definition body, instance, visibility
or public import changes. The separate composition generalization is recorded in
D5-module-pullback-composition-arbitrary-rings.md. These settings are local and do not change importers' reducibility.
Explicit pullback parameters prevent the elaborator from unfolding scheme-limit
constructions while trying incompatible pullbacks.

## Old

The removed private proof-import lines, verbatim:

```lean
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.CategoryTheory.SiteInverseImageCompositionGenerators
import Sheaf.Paper.IntegralFinitePullbackComposition

```

There were no local irreducibility settings. The public theorem had one `sorry`.
The two public derived-comparison definitions are retained verbatim.

## New

The above private imports are removed; added proof imports provide absolute
Frobenius universal homeomorphisms, prime-field data and exact-derived coherence.
The public theorem's signature is identical and its proof is complete.
All added helper declarations are private and proved. Local settings:

```lean
attribute [local irreducible] proEtaleRingModuleAdjunction
  proEtaleRingModulePullback proEtaleRingModulePullbackObj proEtaleRingModulePullbackMap
attribute [local irreducible] coefficientDirectMap
  proEtaleRingDirectImageMap proEtaleConstantRingComparison
attribute [local irreducible] relativeFrobeniusIso relativeFrobeniusMap
attribute [local irreducible] CategoryTheory.constantSheaf
attribute [local irreducible] constantPushforwardIso constantPullbackIso constantPullbackComp
attribute [local irreducible] iterateFrobenius
attribute [local irreducible] conjugateIsoEquiv conjugateEquiv
attribute [local irreducible] rightMate rightIsoMate
attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryIdIso
```

`coefficientDirectMap` is a private definition of the existing coefficient map,
with its proved constant-section equations. The direct-image isomorphism includes
the explicit module `pushforwardId` comparison. The generic ringed-site section
lemma takes the composite comparison map and its mate equation separately; it
checks the composition calculation on the underlying abelian groups. The
section formulas use the canonical pullback-composition map directly: a local
site-isomorphism alias caused expensive scalar-action conversions. The constant-ring
coherence API keeps the left functors and adjunctions as parameters. The local elaboration option
`Elab.async false` processes the dependent APIs in declaration order. The final
proof respects term transparency and uses Mathlib's type-transparency setting for
morphism-property instances. The open derived equation uses the generic coherence
theorem directly; the iterate equation unfolds only the two small public comparison
definitions and reassociates. This avoids large congruence proofs. No compilation limit or proof-checking rule changes.


## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite` lists the
following three direct or transitive consumers. Its textual-use query for the
public theorem lists this item and FrobeniusTrivializationPullback. Every public
signature and public import is unchanged, so no consumer adaptation is required.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite | D5 | One hole closed. |
| Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback | unclaimed | No semantic or interface change. |
| Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization | unclaimed | No semantic or interface change. |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | E8 | No semantic or interface change. |

## Status

landed 20261020T221121-L-4146761 2026-10-20 (merge of deliver/D5/Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite)
