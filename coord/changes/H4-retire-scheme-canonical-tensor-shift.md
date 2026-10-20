# AlgebraicGeometry.schemeCanonicalTensorShift

## Reason

Retirement item `retire:Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift` in
`coord/retire-items.tsv`, under the human's 2026-10-20 retirement hand-off.
The upstream twin now has exactly the same module body after the copyright header,
including its public imports, declaration signature, attributes and definition body.
The earlier DIFFERENT classification predates retirement of the independent-universe
localization copy. The canonical construction still uses the same Koszul localization
and preserves independence of the derived-category universe.

## Old

The withdrawn module publicly imported
`WeilConjectures.AlgebraicGeometry.DerivedTensorStructure` and
`WeilConjectures.AlgebraicGeometry.DerivedTensorShiftIndependentUniverse`, and defined:

```lean
@[instance_reducible]
noncomputable def schemeCanonicalTensorShift (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    (curriedTensor (schemeDerivedCategory X)).CommShift₂Int := by
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  haveI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  haveI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  haveI := schemeModule_hasFunctorialFlatResolution X
  haveI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  exact DerivedCategory.commShift₂CurriedTensor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
```

Seven direct consumers imported:

```lean
public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
```

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/SchemeCanonicalTensorShift.lean` through
`deleted.txt`. Keep the declaration supplied by
`WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShift` unchanged. Its signature,
attributes and body are verbatim the definition above. All seven direct consumers now use:

```lean
public import WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShift
```

Reattach `def-sc-scheme-canonical-tensor-shift` to that upstream module and the same
`AlgebraicGeometry.schemeCanonicalTensorShift` declaration. No node statement or
mathematical dependency changes. The unit's realized route is preserved.

A sandbox-only compatibility probe imports the upstream twin and reproduces the
previous construction as `AlgebraicGeometry.oldSchemeCanonicalTensorShift`. For arbitrary
`X : Scheme.{u}` and independent `HasDerivedCategory.{w}`, Lean proves
`oldSchemeCanonicalTensorShift X = schemeCanonicalTensorShift X` by `rfl`.
Both constructions print only `propext`, `Classical.choice`, and `Quot.sound`.
No nonempty-scheme, boundedness or same-universe hypothesis enters this equality,
so it also applies to the empty scheme and zero representatives.

A source import-closure comparison removes only the withdrawn Sheaf module and adds
only its upstream twin. All their other transitive modules coincide, so the migration
introduces no extra pair of duplicate modules into a consumer environment.
All seven migrated files are compiled in dependency order through `lcompile.py`.
The additional wrap in the associator file repairs its existing 105-character line
without changing any tokens in its statement or proof.

No upstream source is edited. Target signatures stay unchanged. Because a definition
in the targets' dependency closure is retired, the target meaning review should use
the identical source bodies and the Lean definitional-equality check above.

## Users

The table includes all twelve modules reported by
`tools/downstream.py Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift --uses
AlgebraicGeometry.schemeCanonicalTensorShift`. All seven direct consumers were
unclaimed when their holders were checked through `stage3_delivery.claim_holder`.
They are adapted only as described in the table; the other five files stay untouched.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundedFlatShiftRepresentative | unclaimed | Indirect consumer; same canonical data and transitive imports. |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitEquality | unclaimed | Indirect consumer; same canonical data and transitive imports. |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitData | unclaimed | Indirect consumer; same canonical data and transitive imports. |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumModels | unclaimed | Indirect consumer; same canonical data and transitive imports. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitAssociativity | unclaimed | Indirect declaration user; same canonical data and transitive imports. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso | unclaimed | Replace its public import with the upstream twin; body unchanged. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator | unclaimed | Replace its public import; wrap an existing overlong signature line. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne | unclaimed | Replace its public import with the upstream twin; body unchanged. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftProperties | unclaimed | Replace its public import with the upstream twin; body unchanged. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftRightUnitor | unclaimed | Replace its public import with the upstream twin; body unchanged. |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare | unclaimed | Replace its public import with the upstream twin; body unchanged. |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization | unclaimed | Replace its public import with the upstream twin; body unchanged. |

The retired item is assigned to H4.

## Status

landed 20261020T162913-L-3674245 2026-10-20 (merge of deliver/H4/Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift)
