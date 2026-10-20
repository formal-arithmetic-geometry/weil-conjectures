# AlgebraicGeometry.Scheme.tateInverseLimitBaseChange proof commands

## Reason

The completed proof introduces private helpers, two proved private instances for
the private constant-sheaf unit, local transparency attributes, and the scoped
change-of-rings notation. Preflight classifies the instances and the added
commands conservatively as changes requiring a record. This record documents
them for the independent reader. No existing public signature, definition body,
or public import changes, and no target statement changes.

The instances are propositions proved by the existing constant-sheaf unit API.
They provide local injectivity and local surjectivity used by the private
restriction-of-scalars Hom equivalence. The local irreducibility attributes keep
large adjunction and tensor constructions folded after their APIs are proved;
they do not change the constructed objects or persist as global transparency
attributes. The scoped opening only supplies notation within this module.

## Old

No corresponding private instances, local irreducibility commands, or
`open scoped ChangeOfRings` command occurred in this module. Existing public
declarations retain their old signatures and definition bodies verbatim up to
whitespace; their theorem proofs formerly contained twelve holes.

## New

The added instances are:

```lean
private instance (T : Scheme.{u}) (R : Type u) [CommRing R] :
    Presheaf.IsLocallyInjective (ProEt.topology T) (constantUnit T R) :=
  adicLisseConstantUnit_locallyInjective T (ULift.{u + 1, u} R)

private instance (T : Scheme.{u}) (R : Type u) [CommRing R] :
    Presheaf.IsLocallySurjective (ProEt.topology T) (constantUnit T R) :=
  adicLisseConstantUnit_locallySurjective T (ULift.{u + 1, u} R)
```

The added scoped opening and local attributes, placed at the appropriate points
after the relevant private APIs have been established, are:

```lean
open scoped ChangeOfRings
attribute [local irreducible] proEtaleRingModulePullback proEtaleModuleInverseImage
  proEtaleRingModuleAdjunction
attribute [local irreducible] restrictionToTensor
attribute [local irreducible] tensorUnit
attribute [local irreducible] restrictHomEquiv
attribute [local irreducible] directScalarIso tensorPullbackHomEquiv
attribute [local irreducible] tateTensorMap
attribute [local irreducible] tensorHomEquiv tensorPresheafHomEquiv tensorToRestriction
attribute [local irreducible] reductionUnit
attribute [local irreducible] tateReduction
attribute [local irreducible] quotientPullbackHomEquiv
attribute [local irreducible] tatePullbackId
attribute [local irreducible] exchangeModuleComposition
attribute [local irreducible] tatePullbackComp
```

Both instances refer to the new private definition `constantUnit`, an abbreviation
of the existing `adicLisseConstantUnit`; no public definition uses this helper.
The preflight's global-instance classification is retained for reader review;
the proof does not rely on these instances being available to other modules.

## Users

`python3 -B tools/downstream.py Sheaf.Paper.TateInverseLimitBaseChange --uses
constantUnit tatePullbackComp tateTensorMap` reports zero downstream modules in
the current source checkout. It finds the latter two public names only in the
item itself; the new private helper is absent from the old source. No consumer
requires adaptation. The parent proof in the DAG can use the unchanged public
API when it is implemented.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TateInverseLimitBaseChange | B9 | Twelve theorem proofs completed; private proof infrastructure and local commands added; public signatures and definition bodies unchanged. |

## Status

landed 20261020T131940-L-1393758 2026-10-20 (merge of deliver/B9/Sheaf.Paper.TateInverseLimitBaseChange)
