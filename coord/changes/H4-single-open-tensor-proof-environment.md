# single_open_tensor_coefficient_coherence proof environment

## Reason

The proof uses the existing pinned counits and tensor pullbacks. Their dependent
implementation types are large, so private helper proofs keep these definitions
folded while identifying the module categories and single embeddings explicitly.
All added reducibility attributes and elaboration options are confined to a
section that ends before the existing public theorem. The public theorem has
exactly its original signature, visibility and imports. Every added declaration
is a proved private theorem. There is no definition or instance change.

The checker treats source attribute and option commands as interface-sensitive;
this record documents those commands. They change no exported mathematical API,
and require no downstream adaptation or target-statement review.

## Old

The module had no private helper section or proof-specific local attributes.
The only public theorem ended with `:= by sorry`.

## New

The private helper section uses:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option cleanup.letToHave false
set_option maxRecDepth 2048

attribute [local irreducible] derivedPullback Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh
  CochainComplex.singleFunctors DerivedCategory.singleFunctors
  HomotopyCategory.singleFunctors SingleFunctors.postcomp

attribute [local irreducible] Scheme.picardTermwiseSingleMap Scheme.picardTermwiseCounit
  Scheme.Modules.canonicalSinglePullbackMap
```

The naturality helper has a declaration-scoped heartbeat budget of 600000 for
its large selected-counit type. The single-file wall-clock limit remains 60 seconds.
The existing public theorem is proved by the two already imported dependency
statements, with the private helpers supplying normalization and category algebra.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence | H4 | Its one hole is closed; existing signature and visibility are identical. |
| Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow | unclaimed | Its use of the unchanged theorem is unaffected; no adaptation. |

No public declaration body other than the theorem proof is changed, and the local
attributes are not inherited by importers. For the H10 return, the exact base
source of `StandardSingleOpenRelativeArrow.lean` was compiled unchanged against
the delivered item in a fresh `/tmp` sandbox: item 38.2 seconds, downstream
21.3 seconds, both clean. The complete base item, base downstream module and
base node JSON, with commit provenance and hashes, are embedded in report.md
for an independent review that does not require the missing original commit.

## Status

landed 20261014T110246-L-1722338 2026-10-14 (merge of deliver/H4/Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence)
