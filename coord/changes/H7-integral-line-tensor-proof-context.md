# WeilConjectures.integralLineTensorComparison proof context

## Reason

The combination proof repeatedly encountered expensive unfolding of the chosen
coefficient, reduction, tensor, completion and representative constructions. Local
irreducibility attributes let it use the recorded equations of these constructions.
The static interface scanner treats any added `attribute` command as a possible
interface change and requests this record. These attributes are local to this file;
no existing statement, definition body, visibility or public import is changed.

## Old

The existing proof context, verbatim, starts as follows:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
open IntegralOnSlice
```

There were no local irreducibility attributes after the existing definitions.
Every existing definition and the theorem signature retain their original text.

## New

The old context is retained. The following proof-context command is added after
all existing definitions and before the new proved private helpers:

```lean
attribute [local irreducible] SheafOfModules.monoidalCategory coefficientTotalTensor
  IntegralOnSlice.duality IntegralOnSlice.completion integralLineRepresentativeIso
  IntegralOnSlice.ring IntegralOnSlice.finite IntegralOnSlice.reductionWitness
  IntegralOnSlice.reduction
```

The command changes proof elaboration inside this file. It does not export an
attribute change to any importing module. The original theorem signature and all
existing definition bodies were compared verbatim against the shared source.
Private proof imports and private proved helpers implement the new combination
proof; the public imports are preserved.

## Users

`tools/downstream.py Sheaf.Paper.IntegralLineTensorComparison --uses
integralLineTensorComparison integralLineRepresentativeIso` lists these five
transitive importers. Neither declaration is mentioned by any of them. The claim
records listed all five as unclaimed when checked. None is adapted or needs an
adaptation: local proof attributes do not change their elaboration environment,
and every public statement and construction retains its existing meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | No adaptation; public interface unchanged. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | No adaptation; public interface unchanged. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | No adaptation; public interface unchanged. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | No adaptation; public interface unchanged. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | No adaptation; public interface unchanged. |

## Status

landed 20261020T211732-L-3495151 2026-10-20 (merge of deliver/H7/Sheaf.Paper.IntegralLineTensorComparison)
