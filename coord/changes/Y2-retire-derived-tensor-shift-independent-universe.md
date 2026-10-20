# DerivedCategory.IndependentTensorShift.commShift₂CurriedTensor

## Reason

Retirement item `retire:Sheaf.AlgebraicGeometry.DerivedTensorShiftIndependentUniverse`
in `coord/retire-items.tsv`, authorized by the human's 2026-10-20 retirement hand-off.
The original reason for this duplicate has disappeared: the upstream construction now
has independent Grothendieck and localization universes `s` and `w`. Its public API
lives in `DerivedCategory.TensorCommShift₂`, and its final instance is
`DerivedCategory.commShift₂CurriedTensor`.

The declared twin `WeilConjectures.AlgebraicGeometry.DerivedTensorShiftIndependentUniverse`
publicly imports `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`,
which contains all the required constructions. No compatibility copy is needed.

## Old

The retired module's declarations and section setup were:

```lean
namespace DerivedCategory.IndependentTensorShift

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{s} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

variable [HasColimitsOfSize.{0, 0} C]

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

namespace TensorCommShift₂

/-- The localization functor `K(C) ⥤ D(C)` precomposed with the quotient
`CochainComplex C ℤ ⥤ K(C)`. -/
noncomputable abbrev L : CochainComplex C ℤ ⥤ DerivedCategory C :=
  HomotopyCategory.quotient C (.up ℤ) ⋙ Qh

instance : (L C).IsLocalization (HomologicalComplex.quasiIso C (.up ℤ)) :=
  Functor.IsLocalization.of_iso _ (quotientCompQhIso C).symm

/-- The localization functor restricted to K-flat cochain complexes. -/
noncomputable abbrev LKFlat : CochainComplex.KFlat C ⥤ DerivedCategory C :=
  CochainComplex.ιKFlat C ⋙ L C

instance : (LKFlat C).IsLocalization (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat :=
  inferInstanceAs (((HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat.functor ⋙
    L C).IsLocalization _)

noncomputable instance : (curriedTensor (CochainComplex C ℤ)).CommShift₂Int :=
  inferInstanceAs ((curriedTensor C).map₂CochainComplex.CommShift₂Int)

/-- The tensor product of a K-flat complex with a complex, followed by the localization functor:
the bifunctor which is localized to the derived tensor product. -/
noncomputable abbrev F : CochainComplex.KFlat C ⥤ CochainComplex C ℤ ⥤ DerivedCategory C :=
  (CochainComplex.ιKFlat C ⋙ curriedTensor (CochainComplex C ℤ)) ⋙
    (Functor.whiskeringRight _ _ _).obj (L C)

noncomputable instance : (F C).CommShift₂Int := Functor.CommShift₂.postcompInt _ _

/-- The comparison `Qh P ⊗ᴸ Qh K ⟶ Qh (P ⊗ K)` for a K-flat complex `P` and a complex `K`. -/
noncomputable def liftingIsoHom :
    (((Functor.whiskeringLeft₂ _).obj (LKFlat C)).obj (L C)).obj
      (curriedTensor (DerivedCategory C)) ⟶ F C :=
  (((Functor.whiskeringLeft₂ (DerivedCategory C)).obj
    (CochainComplex.ιKFlat C ⋙ HomotopyCategory.quotient C _)).obj
      (HomotopyCategory.quotient C _)).map (Functor.LaxMonoidal.μNatTrans Qh)

instance : IsIso (liftingIsoHom C) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left Qh _ _ _
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2)

noncomputable instance lifting :
    Localization.Lifting₂ (LKFlat C) (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
      (HomologicalComplex.quasiIso C (.up ℤ)) (F C) (curriedTensor (DerivedCategory C)) where
  iso := asIso (liftingIsoHom C)

end TensorCommShift₂

open DerivedCategory.IndependentTensorShift.TensorCommShift₂ in
/-- The derived tensor product commutes with the shifts by `ℤ` in both variables, with the
sign `(-1) ^ (p * q)` when shifting the first variable by `p` and the second by `q`. It is
induced through the localization functors by the commutation with shifts of the tensor
product of cochain complexes (`Functor.commShift₂OfLocalization`).
Source: Stacks Project, Tag 06YH, localization of total tensor products.
(blueprint: lem-sc-derived-tensor-shift-independent-universe). -/
@[instance_reducible]
noncomputable def commShift₂CurriedTensor :
    (curriedTensor (DerivedCategory C)).CommShift₂Int :=
  Functor.commShift₂OfLocalization (LKFlat C) (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (HomologicalComplex.quasiIso C (.up ℤ)) (F C) _ .int

attribute [local instance] commShift₂CurriedTensor


end DerivedCategory.IndependentTensorShift
```

The direct consumer imported:

```lean
public import Sheaf.AlgebraicGeometry.DerivedTensorShiftIndependentUniverse
```

and its `schemeCanonicalTensorShift` definition ended with:

```lean
  exact DerivedCategory.IndependentTensorShift.commShift₂CurriedTensor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
```

## New

Withdraw the old module through `deleted.txt`. The direct consumer now imports:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedTensorShiftIndependentUniverse
```

and its existing definition, with identical signature, ends with:

```lean
  exact DerivedCategory.commShift₂CurriedTensor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
```

In the four other affected consumers, replace references to
`DerivedCategory.IndependentTensorShift.TensorCommShift₂` by
`DerivedCategory.TensorCommShift₂`. The existing private proof namespaces remain;
inside them the local-instance command now resolves the parent namespace's upstream
`DerivedCategory.commShift₂CurriedTensor`. No public theorem signature changes and
all proofs are retained. Existing overlong local-instance declarations in the binary
square and normalization modules are wrapped without changing their tokens.

The upstream declarations used in place of the deleted declarations are:

| deleted API | upstream API |
| --- | --- |
| `IndependentTensorShift.TensorCommShift₂.L` | `TensorCommShift₂.L` |
| `IndependentTensorShift.TensorCommShift₂.LKFlat` | `TensorCommShift₂.LKFlat` |
| `IndependentTensorShift.TensorCommShift₂.F` | `TensorCommShift₂.F` |
| `IndependentTensorShift.TensorCommShift₂.liftingIsoHom` | `TensorCommShift₂.liftingIsoHom` |
| `IndependentTensorShift.TensorCommShift₂.lifting` | `TensorCommShift₂.lifting` |
| `IndependentTensorShift.commShift₂CurriedTensor` | `commShift₂CurriedTensor` |

All names in the table are relative to `DerivedCategory`. Instance search supplies
the corresponding upstream localization, invertibility, and shift instances.
The existing DAG node's Lean attachment points at the declared upstream twin and
`DerivedCategory.commShift₂CurriedTensor`; its statement and dependencies stay the same.

A sandbox-only Lean compatibility probe imports both versions and proves by `rfl`
that both final `CommShift₂Int` structures and both `liftingIsoHom` maps are equal,
for arbitrary independent universes. Thus the exported scheme construction has
identical mathematical data. The probe also reports only `propext`,
`Classical.choice`, and `Quot.sound` for both upstream declarations. The probe is
not part of the delivered library. Its two comparison goals are:

```lean
example : DerivedCategory.IndependentTensorShift.commShift₂CurriedTensor C =
    DerivedCategory.commShift₂CurriedTensor C := by
  rfl

example : DerivedCategory.IndependentTensorShift.TensorCommShift₂.liftingIsoHom C =
    DerivedCategory.TensorCommShift₂.liftingIsoHom C := by
  rfl
```

A source import-closure comparison at `SchemeCanonicalTensorShift` removes only
the retired module and adds only its upstream wrapper. In particular, this delivery
introduces no additional pair of duplicate implementation modules into an importer.

## Users

All holders below were checked with `stage3_delivery.claim_holder` before editing.
The list includes every downstream module reported by `tools/downstream.py`,
including all five declaration users and every adapted module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundedFlatShiftRepresentative | unclaimed | Indirect consumer; unchanged, same construction and public imports available. |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitEquality | unclaimed | Indirect consumer; unchanged, same construction and public imports available. |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitData | unclaimed | Indirect consumer; unchanged, same construction and public imports available. |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumModels | unclaimed | Indirect consumer; unchanged, same construction and public imports available. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitAssociativity | unclaimed | Indirect consumer; unchanged, same construction and public imports available. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso | unclaimed | Indirect consumer; unchanged, same construction and public imports available. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift | unclaimed | Replace its public import and the construction name; signature unchanged. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator | unclaimed | Indirect consumer; unchanged, same construction and public imports available. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne | unclaimed | Indirect consumer; unchanged, same construction and public imports available. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftProperties | unclaimed | Open the upstream localization namespace in private proof setup. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftRightUnitor | unclaimed | Use the upstream localization namespace in the two private helper openings. |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare | unclaimed | Open the upstream localization namespace in private proof setup. |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization | unclaimed | Use upstream liftingIsoHom in the private tensorator invertibility proof. |

The item itself is held by Y2. No upstream module is changed. Target statements are
unchanged. Since a definition in their dependency closure is replaced, the target
meaning review can check this record and the definitional-equality probe; the data
of the replacement are identical.

## Status

landed 20261020T150713-L-2576439 2026-10-20 (merge of deliver/Y2/Sheaf.AlgebraicGeometry.DerivedTensorShiftIndependentUniverse)
