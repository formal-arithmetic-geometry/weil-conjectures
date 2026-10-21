# Sheaf.Paper.SupportedCupFunctoriality proof elaboration context

## Reason

The twelve completed proofs need local access to the selected sheaf and derived
category instances without repeated expansion of their large constructions.
The static interface checker reports the added `open`, `universe`, and local
`attribute` commands as a visible-command change. These commands are confined
to proof sections. No original declaration signature, non-theorem body, public
import, or exported attribute changes. No target changes meaning.

## Old

There were no `CoefficientProof`, `ClosedSupportProof`, `SupportMapProof`, or
`SequenceProof` sections and no local attributes in this module. The module's
existing global options, universe declaration, and namespace openings remain
verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
```

## New

Within the new proof sections, use the following local attribute commands
(the closed-support and support-map sections share the same reducibility list):

```lean
attribute [local reducible] functorialCupHasDerived functorialCupDerivedMonoidal
  functorialCupMonoidal functorialCupAbelian functorialCupCategory
  functorialCupMonoidalPreadditive functorialCupSymmetric functorialCupClosed
  functorialCupFlatResolutions functorialCupMultiplication functorialCupSource
```

```lean
attribute [local reducible] functorialCupCategory functorialCupAbelian
  functorialCupMonoidal functorialCupSymmetric functorialCupClosed
  constant constantEtale functorialCupConstant functorialCupComparisonFunctor
  functorialCupSource functorialCupRestriction functorialCupInverseImage
  functorialCupConstantPullback
```

```lean
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
```

```lean
attribute [local reducible] functorialCupCategory functorialCupAbelian
  constant constantEtale functorialCupConstant functorialCupSource
  functorialCupRestriction functorialCupInverseImage functorialCupConstantPullback
  functorialCupComparisonFunctor functorialCupOpenExtension functorialCupOpenSource
  functorialCupOpenInclusion
```

Each reducibility command is immediately preceded by
`set_option allowUnsafeReducibility true in`. This permits a local elaboration
attribute on the existing instances; it does not bypass kernel checking or change
their bodies. The sections close before the subsequent public definitions.
The coefficient section uses `set_option backward.isDefEq.respectTransparency true`.
The closed-source and etale-exchange helper sections use
`set_option backward.isDefEq.respectTransparency.types false`; selected private
helpers also scope `backward.isDefEq.respectTransparency false` and
`backward.defeqAttrib.useBackward true` for their proofs. These are elaboration
settings only. The added namespace and universe commands are:

```lean
open ProEtale
universe c1 c2 c3 c4 v1 v2 v3 v4
```

inside `ClosedSourceNormalization`, and `open Etale` inside
`EtaleSourceNormalization` and `EtaleExchangeNormalization`. The new universe
parameters are used by fully proved private generic helpers. No public declaration
acquires a universe parameter. Every added helper is private and proved; no
private helper occurs in a public definition body or signature.

## Users

`tools/downstream.py Sheaf.Paper.SupportedCupFunctoriality` reports the following
16 transitive consumers. Their statements and mathematical meaning do not change;
no consumer file is edited. The claim records were read on 2026-10-21.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SupportedCupFunctoriality | P9 | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Same public interface and definitions; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Same public interface and definitions; no adaptation. |

## Status

landed 20261021T140853-L-2766708 2026-10-21 (merge of deliver/P9/Sheaf.Paper.SupportedCupFunctoriality)
