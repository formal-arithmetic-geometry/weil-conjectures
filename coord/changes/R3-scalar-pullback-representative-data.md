# AlgebraicGeometry.Etale scalar/pullback representative data

## Reason

The separate K-flat representative computation needs exactly the ordinary scalar,
cochain, geometric counit and coefficient-unit maps specified by the assigned
module. Sharing these constructions permits that module to import the representative
computation without an import cycle. Duplicating their expanded formulas in the new
theorem type made kernel checking of the parent transport proof take 42 seconds
by itself. Using the same named data fixes that duplication and supplies an API for
the comparison maps. No proof is divided to meet a time limit.

## Old

The following definitions occurred in `Sheaf.Paper.PurEtaleScalarMateProjection`:

```lean
/-- The ordinary scalar/pullback identification, conjugate to the sectionwise
restriction/direct-image identity under the two composite adjunctions.
Source: Stacks 07A4 (blueprint: lem-pur-etale-scalar-mate-projection). -/
def scalarSheafPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    ProEtale.etaleSheafExtendScalars φ W ⋙ upperStar (ModuleCat.{u + 1} B) f ≅
      upperStar (ModuleCat.{u + 1} A) f ⋙ ProEtale.etaleSheafExtendScalars φ Z :=
  (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ Z))
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ W).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))).symm
    (lowerStarCompRestrictScalarsIso φ f).symm

/-- The same comparison on actual cochain complexes.
Source: Stacks 07A4 (blueprint: lem-pur-etale-scalar-mate-projection). -/
def scalarSheafPullbackComplexIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :=
  Functor.mapHomologicalComplexCompIso (scalarSheafPullbackIso φ f) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (upperStar (ModuleCat.{u + 1} A) f ⋙
        ProEtale.etaleSheafExtendScalars φ Z)) (.up ℤ)).symm

/-- The geometric derived counit, with the homotopy quotient comparison included.
Source: Stacks 07A4 (blueprint: lem-pur-etale-scalar-mate-projection). -/
def scalarGeometricRepresentative
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) :=
  (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    _root_.DerivedCategory.Qh.map
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P)

/-- The specified identification f_A^{-1}B_W[0] = B_Z[0].
Source: Stacks 07A4 and 07A6 (blueprint: lem-pur-etale-scalar-mate-projection). -/
def scalarCoefficientPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj (scalarCoefficient φ W) ≅
      scalarCoefficient φ Z :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app _ ≪≫
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((upperStarRestrictScalarsIsoSheaf φ f).app (𝟙_ _) ≪≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapIso
          (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) f)).symm)

```

## New

The exact definitions above occur in
`Sheaf.Paper.ScalarPullbackRepresentativeData`. Their names, universes, signatures,
visibility and bodies are byte-identical; only docstring blueprint ownership points
to the new definition node. The original module publicly imports the data module
and retains every original public import, so its exported API is preserved.
The independent representative theorem now refers to these constants rather than
repeating their values. No target meaning or target statement changes.

The modules locally make chosen adjoints, derived functors, `derivedTensor`,
`upperStar` and `lowerStar` irreducible while elaborating diagrams. These are local
proof elaboration attributes, not changes to exported reducibility or instances.

## Users

The current source scan of both library roots finds the original item and its
users `AcyclicFlatProperCoefficientModel` and `ProperFiniteCoefficientExtension`.
The landing return additionally identifies
`Sheaf.SecSmoothPurity.ScalarPullbackTensorCompatibility` as a user of
`scalarSheafPullbackIso` and `scalarCoefficientPullbackIso`; it is included below
although its source and claim are absent from this machine's current shared snapshot.
The added representative theorem is another consumer. No consumer source adaptation
is required: the four definitions retain their names, types and values, and remain
publicly available through the original module's public reexport. The two available
external consumers are checked unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurEtaleScalarMateProjection | R3 | Own item; public reexport; complete combining proof. |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | U3 | Original source unchanged; same imported comparison name and value. |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension | F1 | Original source unchanged; same coefficient identification. |
| Sheaf.SecSmoothPurity.ScalarPullbackTensorCompatibility | no claim in current snapshot | Landing-return user of scalarSheafPullbackIso and scalarCoefficientPullbackIso; identical names, signatures and values remain available through the public reexport. No adaptation. |
| Sheaf.Paper.ScalarTensorPullbackNormalization | R3 (new) | Uses the specified shared comparison data directly. |

## Status

landed 20261020T233217-L-906112 2026-10-20 (merge of deliver/R3/Sheaf.Paper.PurEtaleScalarMateProjection)
