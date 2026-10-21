# AlgebraicGeometry.ProEtale.integralInverseImageComparison_composition

## Reason

The proof transports two ordinary exact-functor diagrams to derived categories.
Its proved private helpers use abstract category and derived-category universes,
scoped variables in `section AbstractPasting`, and a private additive-instance
helper for a bundled exact functor. Preflight classifies those commands and the
instance registration as requiring a change record. This record documents them
for the independent reader. This is the G3-held item; no other module is edited.

All four existing public signatures, all existing public definitions, and all
public imports remain verbatim. Every added helper is private and proved or
concretely constructed. No data is selected from an undetermined existence claim.

## Old

The universe command, verbatim:

```lean
universe u
```

There was no `CompositionVertex`, no `AbstractPasting` section and no
`exactFunctor_additive` declaration. The other existing top-level `variable`,
`open`, `attribute`, and option commands are unchanged. The only existing proof
body replaced is that of `integralInverseImageComparison_composition`; the
already proved unique compositor is preserved.

## New

```lean
universe u a b c
```

The new private finite vertex type indexes two finite exact-functor pastings.
The abstract section begins with the following exact commands and helper:

```lean
variable {A0 A1 A2 A3 A4 A5 : Type a}
  [Category.{b} A0] [Category.{b} A1] [Category.{b} A2]
  [Category.{b} A3] [Category.{b} A4] [Category.{b} A5]
  [Abelian A0] [Abelian A1] [Abelian A2] [Abelian A3] [Abelian A4] [Abelian A5]
  [HasDerivedCategory.{c} A0] [HasDerivedCategory.{c} A1] [HasDerivedCategory.{c} A2]
  [HasDerivedCategory.{c} A3] [HasDerivedCategory.{c} A4] [HasDerivedCategory.{c} A5]

private instance exactFunctor_additive {A B : Type a} [Category.{b} A] [Category.{b} B]
    [Abelian A] [Abelian B] (F : A ⥤ₑ B) : F.obj.Additive :=
  exactFunctor_le_additiveFunctor A B _ F.property
```

`end AbstractPasting` closes the generic variable scope before either concrete
specialization. The instance is private; its proof is the existing
`exactFunctor_le_additiveFunctor`, with no new mathematical hypothesis or axiom.
It supplies additivity only while constructing the private derived-pasting
helpers. No existing attribute is removed or changed. The delivery is intended
for CODEX review rather than AUTO classification.

## Users

`tools/downstream.py Sheaf.Paper.IntegralInverseImageComparisonComposition --uses
integralInverseImageComparison_composition exactFunctor_additive` reports 11
transitive importing modules. The theorem name occurs only in this item, and
there are no external occurrences of the private additive-helper name. No
consumer's signature or proof needs adaptation: the original public interface
is identical, and the new generic section variables do not escape their scope.
The DAG parents and unit remain attached; no module is withdrawn.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralInverseImageComparisonComposition | G3 | Original theorem proved; private proof helpers added |

The transitive importers reported by the script are
`Sheaf.DeligneLaumon.Reduction.FiniteMapPurity`,
`Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity`,
`Sheaf.Paper.A1FiniteEtaleWeilFibreComparison`,
`Sheaf.Paper.CompactSupportSystemRealizationNormalization`,
`Sheaf.Paper.ConstantExtensionCompactComparison`,
`Sheaf.Paper.ConstantExtensionMixedDescent`,
`Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`,
`Sheaf.Paper.ConstantGeometricStalkUnit`, `Sheaf.Paper.DlConstantFieldCharts`,
`Sheaf.Paper.IntegralPointTransportTowerPowers`, and
`Sheaf.Paper.WeilConstantExtensionFrobenius`. They are not adapted in this packet.

## Status

landed 20261021T225131-L-3777125 2026-10-21 (merge of deliver/G3/Sheaf.Paper.IntegralInverseImageComparisonComposition)
