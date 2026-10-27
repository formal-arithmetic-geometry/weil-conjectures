# AlgebraicGeometry.ringComplexScalarAugmentation

## Reason

Construct the augmentation after scalar extension explicitly, so that the derived model
comparison uses the same augmentation whose value on the sheafification unit is normalized.

## Old

No declaration of this name existed. Existing declarations and their signatures stay identical.

## New

The new module `Sheaf.Paper.RingComplexScalarAugmentation` defines the unit multiplication
by the existing semilinear adjunction lift. It defines `ringComplexScalarSingle` by applying
`single` to that multiplication and the additive single-complex comparison, and defines
`ringComplexScalarAugmentation φ ε` as the scalar extension of ε followed by that map.
`ringComplexScalarAugmentation_one_tmul` proves its normalization.

```lean
def ringComplexScalarAugmentation {A B : CommRingCat.{u}} (φ : A →+* B)
    {P : CochainComplex (RingSiteModules A) ℤ} (ε : P ⟶ ringComplexSingle A) :
    ringComplexExtensionComplex φ P ⟶ ringComplexSingle B :=
  ((ringComplexExtension φ).mapHomologicalComplex (.up ℤ)).map ε ≫
    ringComplexScalarSingle φ
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingComplexOrderedScalarIso | N2, new | Augmented cochain comparison |
| Sheaf.Paper.RingComplexCechScalarModel | N2 | Uses the canonical augmentation and normalization |

There are no existing importers of the new module. No existing interface or target changes.

## Status

landed 20261026T092116-L-3401753 2026-10-26 (merge of deliver/N2/Sheaf.Paper.RingComplexCechScalarModel)
