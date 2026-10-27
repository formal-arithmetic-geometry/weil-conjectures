# CategoryTheory.ScalarLocalization.category

## Reason

Concrete tensor and Weil comparison proofs repeatedly reduce the tensor Hom type of
scalar localization. Naming that type separately lets the kernel share its reduction.
`tensorHom` is exactly the existing tensor product, and is reducible for instance
inference. Its arguments retain the localized objects until the alias is unfolded.
The category differs only by calling this definition in its Hom field.
All identities, composition, laws, universes, existing signatures and public imports
are unchanged. Unfolding `tensorHom` gives the old category definition verbatim.
The module is unclaimed. This adds no choices or proof obligations.

Every target using this category therefore retains its original meaning; the
independent definition review can check the displayed definitional equality.

## Old

```lean
noncomputable instance category : Category.{max r v} (ScalarLocalization R C p) where
  Hom K L := Localization.Away p ⊗[R] (K.obj ⟶ L.obj)
  id K := (1 : Localization.Away p) ⊗ₜ[R] 𝟙 K.obj
  comp {K L M} f g := composition R C p K.obj L.obj M.obj g f
  id_comp {K L} f := (composition_laws R C p).1 K.obj L.obj f
  comp_id {K L} f := (composition_laws R C p).2.1 K.obj L.obj f
  assoc {K L M N} f g h := (composition_laws R C p).2.2 K.obj L.obj M.obj N.obj f g h
```

## New

```lean
/-- The tensor Hom type, named before the category instance to share its reduction.
Source: the displayed Hom formula of `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
@[reducible] def tensorHom (K L : ScalarLocalization R C p) : Type (max r v) :=
  Localization.Away p ⊗[R] (K.obj ⟶ L.obj)

/-- The tensor-Hom category, with identities tensored with one and extended composition.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable instance category : Category.{max r v} (ScalarLocalization R C p) where
  Hom K L := tensorHom R C p K L
  id K := (1 : Localization.Away p) ⊗ₜ[R] 𝟙 K.obj
  comp {K L M} f g := composition R C p K.obj L.obj M.obj g f
  id_comp {K L} f := (composition_laws R C p).1 K.obj L.obj f
  comp_id {K L} f := (composition_laws R C p).2.1 K.obj L.obj f
  assoc {K L M N} f g h := (composition_laws R C p).2.2 K.obj L.obj M.obj N.obj f g h
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.ScalarLocalization --uses
CategoryTheory.ScalarLocalization.category` reports 4,928 transitive importers and
36 textual matches. The table includes every reported match and the assigned module.
Several matches are homonyms of `category`, rather than this declaration. For all
implicit consumers as well, unfolding `tensorHom` recovers the identical category;
no existing statement becomes weaker, stronger or different. No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.ScalarLocalization` | unclaimed | Named Hom type; same category fields after unfolding tensorHom. |
| `Sheaf.Paper.AdmissibleHomSubstitution` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.AlgebraicallyClosedCoefficients` | unclaimed | Cached/inherited category instance; objects, Hom types and maps remain definitionally equal. |
| `Sheaf.Paper.AutomorphismSquareRationalScalar` | unclaimed | Unfolds category in simp; the reducible Hom alias preserves the equations. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | Cached/inherited category instance; objects, Hom types and maps remain definitionally equal. |
| `Sheaf.Paper.CompactSupportExchangeDomains` | unclaimed | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.Paper.CompactSupportNormalizedTowerLimit` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.CompositionComparisons` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.ConstantPurityFrobeniusSquare` | F7 | Unfolds category before rfl; both sides have the same reducible Hom alias. |
| `Sheaf.Paper.ConstantScalarStrictUnit` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | Cached/inherited category instance; objects, Hom types and maps remain definitionally equal. |
| `Sheaf.Paper.CtfCoefficientStageSelectors` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.FdHomLinearEquivalence` | unclaimed | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.Paper.FdShiftTriangleReflection` | unclaimed | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.Paper.FiniteProductFieldCoefficientDescent` | unclaimed | Cached/inherited category instance; objects, Hom types and maps remain definitionally equal. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.LocalizedTStructure` | unclaimed | Tensor induction after dsimp; the reducible alias is the same tensor-product type. |
| `Sheaf.Paper.MiddleExchangeProjectionBaseChange` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.NormalizedOrientationPerfectDuality` | unclaimed | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.Paper.OrderedExchangeCoefficientData` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.PbcWeilCategory` | unclaimed | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.QbarCompactSupportBaseChange` | unclaimed | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | U2 | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.RationalPurityPresentation` | W3 | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | S3 | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.Paper.RelativeProductFactors` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.SmoothPurityTowerReductionTranspose` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.SupportedHomPullback` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.TowerTracePurityComparison` | P4 | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.Paper.VerdierPairingThreeTransposes` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.WeilTensorProduct` | unclaimed | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.Paper.WeilTensorWeil` | unclaimed | Local instance/reducibility attributes retain the same constant and signature; no adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenCalculus` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.SixFunctors.AmbientUnderivedClopenPasting` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift` | unclaimed | Search matched another category name or commentary; no explicit use of the changed declaration. |
| `Sheaf.Paper.ProjectionWeilTensorDomainBridge` | R3 | New proof uses the same localized Hom types; compiled in this packet. |

## Status

landed 20261026T070749-L-3655085 2026-10-26 (merge of deliver/R3/Sheaf.Paper.ProjectionWeilTensorDomainBridge)
