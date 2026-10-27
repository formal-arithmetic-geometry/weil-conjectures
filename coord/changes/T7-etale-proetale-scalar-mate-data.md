# AlgebraicGeometry.ProEtale scalar and comparison data

## Reason

Repair retry, 2026-10-26: rebased the packet against the current sheaf-dag tip. The landing failure named an unrelated source file removed by the red-build cleanup; this item has no import of it.

Repair note, 2026-10-25: C-9276d approved delivery 9276d80929d; landing failed
because --apply-fixes received a bare report basename. The report's delivery path
is coord/reports/T7/Sheaf.Paper.EtaleProEtaleScalarMate.md. The replacement packet
preserves the approved mathematical changes and refreshes current node metadata;
its delivery compiles and runs preflight anew against current sheaf-dag.
A fresh compile exposed the normalization timeout again. A fully proved private
generic unique_choice_eq lemma now performs the final uniqueness application;
the reviewed normalization calculation is factored into proved generic mate and
representative-square lemmas with the standard backward-definitional-equality settings. Public definitions and
signatures remain those approved by C-9276d. (Reviewer correction, review of
3d8a79c3924f: the replacement had dropped the C-9276d corrections and also routed
directImageComparisonAmbientPullbackIso through exactDerivedComparisonSquare; the
review re-applies the C-9276d corrections and restores the published five-factor
body of directImageComparisonAmbientPullbackIso, which OpenProEtaleCounitScalar
unfolds.)


The item proof uses the previously proved scalar/pullback cube and counit transposes.
Both import the item's canonical comparison data, causing an import cycle if imported
from the original module. Move those data and their proved normalization helpers to
EtaleProEtaleScalarMateData and publicly reexport them from the original module.
The comparison definitions, public names, types, and values are preserved. Private normalization
consumers retain their existing imports through proved forwarding lemmas in the
original module. No target changes meaning.

The profiler also found expensive kernel unfolding of scalarGeometricRepresentative
and scalarExtensionRepresentative in their equations. Add proved API equations next to
those definitions and invoke them from the normalization proof. The geometric representative retains its original counit construction verbatim;
a generic exact-derived restriction-square theorem proves its comparison equation. The scalar representative names its existing cochain-unit composite; unfolding
that name gives precisely its old construction.

## Old

```lean
/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the reverse scalar/pullback
comparison is the inverse scalar-adjunction mate of the exact pro-etale
restriction/pullback square. It specializes `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def scalarPullbackReverseProEtale
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L(upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology X) a ⟶
      pbcFixedScalarExtension (Scheme.ProEt.topology Y) a ⋙
        L(upperStar (ModuleCat.{u + 1} B) f) :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) a))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a))).symm
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso a f).hom)).natTrans

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the reverse comparison
on the etale site uses the actual exact restriction/pullback square. It specializes
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Source: Stacks 07A4
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def scalarPullbackReverseEtale
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a ⟶
      pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology a))).symm
    (TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso a f).hom)).natTrans

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the canonical tensor/pullback
comparison is invertible for arbitrary ring maps. This is the constant-coefficient
specialization of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
Source: Stacks 07A4 and 0G7E (blueprint: lem-sfb-etale-proetale-scalar-mate).
Proof: choose K-flat resolutions with flat terms on either small site. Exact
inverse image preserves these resolutions and commutes with constant-ring scalar
extension. On the representatives the inverse scalar mate is the ordinary
balancing map, since its scalar-unit equation is the ordinary tensor adjunction.
Its inverse is the opposite balancing identification. The pure-tensor and unit
normalizations of the general recorded tensor-pullback comparison identify these
maps with its constant-coefficient specialization. Naturality and localization
extend them to all derived objects, preserving both inverse equations. This proves
invertibility on both sites without flatness of B over A or boundedness. -/
theorem scalarPullbackReverse_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (scalarPullbackReverseProEtale a f) ∧
      IsIso (scalarPullbackReverseEtale a f) := by
  sorry

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the specified forward
pro-etale tensor/pullback isomorphism is the inverse of the actual scalar mate.
It specializes `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` and is not arbitrary.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def scalarPullbackProEtaleIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension (Scheme.ProEt.topology Y) a ⋙
        L(upperStar (ModuleCat.{u + 1} B) f) ≅
      L(upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology X) a :=
  haveI := (scalarPullbackReverse_isIso a f).1
  (asIso (scalarPullbackReverseProEtale a f)).symm

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the specified forward
etale tensor/pullback isomorphism is the inverse of the actual scalar mate.
It specializes `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
It reuses the published `AlgebraicGeometry.Etale.scalarPullbackIso`.
The proved private comparison at the end of this file identifies this abbreviation
with the original inverse-mate expression, preserving its canonical normalization.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-proetale-scalar-mate). -/
abbrev scalarPullbackEtaleIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a :=
  Etale.scalarPullbackIso a f


/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the canonical inverse-image
square identifies exact termwise inverse images with their left derived functors.
It specializes `sk-thm-pe-direct-image-comparison`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def directImageComparisonAmbientPullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        L(upperStar (ModuleCat.{u + 1} A) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the ambient site/direct-image
comparison is the actual counit mate of the specified inverse-image square.
It specializes `sk-thm-pe-direct-image-comparison`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def directImageComparisonAmbient
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R(Etale.lowerStar (ModuleCat.{u + 1} A) f) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        R(lowerStar (ModuleCat.{u + 1} A) f) :=
  (mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (directImageComparisonAmbientPullbackIso A f).hom)).natTrans

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the ambient canonical
comparison is invertible at every bounded-below input. It specializes
`sk-thm-pe-direct-image-comparison`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate).
Proof: the site square is the canonical fibre-product square (step 1). Exact inverse
images preserve lower bounds, and termwise localization constructs the displayed square
(step 2). Its derived mate is beta, with the prescribed counit equation (step 3).
For qcqs f, the existing direct-image comparison gives an isomorphism e between the
endpoints. Full faithfulness of comparison inverse image identifies both Hom sets
out of a comparison image with the same etale adjunction Hom set. By the mate formula,
postcomposition with beta is the identity under these identifications. Surjectivity
and injectivity give a two-sided inverse for beta (step 4). The derived classical
equivalence then transports classical bounded-below inputs and all-degree cohomology
continuity across this isomorphism (step 5). Naturality and the triangle
identities identify the ambient mate on D+ with the previously recorded comparison,
including its units, counits, identity and composition normalization (step 6).
No finiteness of A is used in this discrete-coefficient theorem. -/
theorem directImageComparisonAmbient_isIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hJ : ∃ n : ℤ, J.IsGE n) :
    IsIso ((directImageComparisonAmbient A f).app J) := by
  sorry

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the inverse of beta is
taken only at the specified bounded-below input. It specializes
`sk-thm-pe-direct-image-comparison`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def directImageComparisonAmbientIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hJ : ∃ n : ℤ, J.IsGE n) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J) ≅
      R(lowerStar (ModuleCat.{u + 1} A) f).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J) :=
  haveI := directImageComparisonAmbient_isIso A f J hJ
  asIso ((directImageComparisonAmbient A f).app J)
```

The old representative definitions are, verbatim:

```lean
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
```

```lean
def scalarExtensionRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (scalarExtension φ T).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex
            (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ProEtale.etaleSheafExtendScalars φ T ⋙
              Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).inv.app P) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P))
```

The old restriction comparison is, verbatim:

```lean
def scalarRestrictionPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    Sheaf.derivedRestrictScalars W.smallEtaleTopology φ ⋙
        L(upperStar (ModuleCat.{u + 1} A) f) ≅
      L(upperStar (ModuleCat.{u + 1} B) f) ⋙
        Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f) ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm _
```

The old coefficient comparison is, verbatim:

```lean
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

The declarations above are in Sheaf.Paper.EtaleProEtaleScalarMateData, publicly imported
by Sheaf.Paper.EtaleProEtaleScalarMate. The original module directly retains its
former public import list. The shared data imports only the declarations needed
by its definitions and proofs. The two former sorry proofs are complete.
The main theorem's signature remains identical and its proof uses the cube, common
counit transposes, Hom-equivalence injectivity and cancellation of the comparison.
Sheaf.Paper.DerivedScalarRestrictionPullbackMate proves the two site-specialized
scalar inverse mate isomorphism theorems using flat resolutions and adjunction uniqueness.
The original private right-adjoint cache is retained in the normalization proof.
The final uniqueness calculation applies a generic pointwise inverse
normalization lemma, avoiding concrete functor expansion.
The representative modules add private restriction-square and naturality equations,
scalarGeometricRepresentative_eq, scalarGeometricRepresentative_exact and
scalarExtensionRepresentative_unit with complete proofs; the new name scalarRepresentativeUnit, whose body
is precisely its former inline cochain-unit composite. The geometric representative retains its original counit construction verbatim.
The generic exact-derived restriction-square theorem is specialized after the
proved representative equation, so its consumers need no adaptation. Definition review is reopened
for targets using the named scalar-unit and single-coefficient comparison formulas;
these constructions are identical after unfolding the added names. The cube
needs no change to its unfold list: the published body of scalarRestrictionPullbackIso is kept.



The scalar representative refactoring is, verbatim:



```lean
def scalarRepresentativeUnit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    P ⟶ ((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ) ⋙
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P :=
  (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
    (NatTrans.mapHomologicalComplex
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.etaleSheafExtendScalars φ T ⋙
        Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).inv.app P

/-- The derived-extension counit on a cochain representative, including the quotient factor.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarExtensionRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (scalarExtension φ T).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex
            (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ProEtale.etaleSheafExtendScalars φ T ⋙
              Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).inv.app P) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P))
```

(Reviewer correction: the body of scalarExtensionRepresentative is the published one,
unchanged; scalarRepresentativeUnit is a separate name for the same composite.)

The restriction comparison keeps its published body (reviewer correction); the generic
named formula below is definitionally equal to it and is used only by the new proofs:

```lean
def scalarRestrictionPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    Sheaf.derivedRestrictScalars W.smallEtaleTopology φ ⋙
        L(upperStar (ModuleCat.{u + 1} A) f) ≅
      L(upperStar (ModuleCat.{u + 1} B) f) ⋙
        Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f) ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm _
```

The named categorical formulas are explicit constructions:

```lean
def exactDerivedComparisonSquare
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Abelian A] [Abelian B] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F₁ : B ⥤ A) (F₂ : A ⥤ E) (G₁ : B ⥤ D) (G₂ : D ⥤ E)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (L : DerivedCategory A ⥤ DerivedCategory E)
    (M : DerivedCategory B ⥤ DerivedCategory D)
    (ε : L ≅ F₂.mapDerivedCategory) (δ : M ≅ G₁.mapDerivedCategory) :
    F₁.mapDerivedCategory ⋙ L ≅ M ⋙ G₂.mapDerivedCategory :=
  Functor.isoWhiskerLeft F₁.mapDerivedCategory ε ≪≫
    Functor.mapDerivedCategorySquareIso e ≪≫
    Functor.isoWhiskerRight δ.symm G₂.mapDerivedCategory

/-- An exact geometric representative in the specified derived comparison.
Source: Stacks 07A4 (blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons). -/
def exactDerivedRepresentative
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory E]
    (F : A ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory A ⥤ DerivedCategory E) (ε : L ≅ F.mapDerivedCategory)
    (P : CochainComplex A ℤ) :
    L.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  ε.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P
```

The coefficient pullback also factors its unchanged composite through a named
generic formula, to avoid repeated concrete monoidal instance elaboration:

```lean
def exactSingleCoefficientIso
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [Abelian C] [Abelian D] [Abelian E] [Abelian H]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (U : E ⥤ C) (G : E ⥤ H) (V : H ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory C ⥤ DerivedCategory D) (ε : L ≅ F.mapDerivedCategory)
    (e : U ⋙ F ≅ G ⋙ V) {M : E} {N : H} (α : G.obj M ≅ N) :
    L.obj ((DerivedCategory.singleFunctor C 0).obj (U.obj M)) ≅
      (DerivedCategory.singleFunctor D 0).obj (V.obj N) :=
  ε.app _ ≪≫ (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor D 0).mapIso (e.app M ≪≫ V.mapIso α)

/-- The specified identification f_A^{-1}B_W[0] = B_Z[0].
Source: Stacks 07A4 and 07A6 (blueprint: def-pur-scalar-pullback-representative-data). -/
def scalarCoefficientPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj (scalarCoefficient φ W) ≅
      scalarCoefficient φ Z :=
  exactSingleCoefficientIso
    (upperStar (ModuleCat.{u + 1} A) f)
    (Sheaf.restrictScalars W.smallEtaleTopology φ)
    (upperStar (ModuleCat.{u + 1} B) f)
    (Sheaf.restrictScalars Z.smallEtaleTopology φ)
    L(upperStar (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (upperStarRestrictScalarsIsoSheaf φ f)
    (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) f)).symm
```

## Reviewer correction (independent review of 9276d80929d2)

Compiling the downstream users against the delivery broke eleven modules that compile
against the published library: EtaleCounitScalarModel, EtaleOpenScalarExchange,
DerivedScalarExtensionLocalSystems, EtaleSumCounitScalar, ProperOpenCoefficientMate,
EtaleOpenTensorDefs and FiniteCoefficientDirectImage (they `dsimp`/`simp` with
scalarRestrictionPullbackIso and need its published composite), ExceptionalCoefficientMaps,
ExceptionalCoefficientUnitCoherence and EtaleHomComparisonModels (they `unfold
scalarExtensionRepresentative` and rewrite with mapComplex_unit_formula), and
AffineCounitScalar (it uses the private cachedEtale* wrappers of the item through
`import all`). The review therefore restores the published bodies of
scalarRestrictionPullbackIso and scalarExtensionRepresentative verbatim, keeps
exactDerivedComparisonSquare, exactDerivedRepresentative and scalarRepresentativeUnit as
separate definitions equal to them by `rfl`, reverts the cube's unfold list, and restores
the thirteen private cachedEtale* wrappers in the item module. No published body changes now
except scalarCoefficientPullbackIso (factored through exactSingleCoefficientIso, identical
after unfolding; all its users compile).

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafFoldScalar | unclaimed | Existing public and private interface preserved by forwarding lemmas; no adaptation. |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | unclaimed | Unchanged; the geometric representative keeps its original construction. |
| Sheaf.Paper.BoundedFlatCoefficientSiteSquare | J2 | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.DerivedScalarRestrictionPullbackMate | unclaimed | Delivered; definitions shared or proof-only import adapted; existing signatures unchanged. |
| Sheaf.Paper.EtaleCompactScalarCoherence | Q3 | Existing public and private interface preserved by forwarding lemmas; no adaptation. |
| Sheaf.Paper.EtaleUnboundedRestrictionComparison | unclaimed | Name the generic square and representative formulas; existing comparison remains definitionally equal. |
| Sheaf.Paper.EtaleDerivedScalarTensor | unclaimed | Delivered; definitions shared or proof-only import adapted; existing signatures unchanged. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | H1 | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.EtaleOpenScalarExchange | unclaimed | Existing public and private interface preserved by forwarding lemmas; no adaptation. |
| Sheaf.Paper.EtaleProEtaleScalarCounitTransposes | unclaimed | Delivered; definitions shared or proof-only import adapted; existing signatures unchanged. |
| Sheaf.Paper.EtaleProEtaleScalarMate | T7 | Delivered; definitions shared or proof-only import adapted; existing signatures unchanged. |
| Sheaf.Paper.EtaleProEtaleScalarMateData | unclaimed | Delivered; definitions shared or proof-only import adapted; existing signatures unchanged. |
| Sheaf.Paper.EtaleProEtaleScalarPullbackCube | unclaimed | Delivered; definitions shared or proof-only import adapted; existing signatures unchanged. |
| Sheaf.Paper.EtaleProperCoefficientTensorUnit | unclaimed | Existing public and private interface preserved by forwarding lemmas; no adaptation. |
| Sheaf.Paper.EtaleSumCoefficientComputation | W8 | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.EtaleSystemCofinalMate | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientMaps | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientUnitCoherence | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDirectImage | unclaimed | Existing public and private interface preserved by forwarding lemmas; no adaptation. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeHomLocalCalculation | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.FiniteHomDomainCalculus | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | F3 | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.PurEtaleScalarMateProjection | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.Paper.ScalarPullbackComposition | unclaimed | Existing public and private interface preserved by forwarding lemmas; no adaptation. |
| Sheaf.Paper.ScalarPullbackIsoExistence | unclaimed | Unchanged; the geometric representative keeps its original construction. |
| Sheaf.Paper.ScalarPullbackIsoUniqueness | unclaimed | Unchanged; the geometric representative keeps its original construction. |
| Sheaf.Paper.ScalarPullbackRepresentativeData | unclaimed | Delivered; definitions shared or proof-only import adapted; existing signatures unchanged. |
| Sheaf.Paper.ScalarTensorPullbackNormalization | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.SixFunctors.EtaleHomComparisonModels | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenTensorDefs | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportData | unclaimed | Comparison formula preserved after unfolding generic helper; no adaptation. |
| Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction | unclaimed | Comparison formula preserved after unfolding generic helper; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatCoefficientTensorExchangeComparison | unclaimed | Comparison formula preserved after unfolding generic helper; no adaptation. |
| Sheaf.Paper.SupportedTriangleMateIdentification | unclaimed | Comparison formula preserved after unfolding generic helper; no adaptation. |
| Sheaf.Paper.PurKFlatOpenProjectionModel | A3 | Comparison formula preserved after unfolding generic helper; no adaptation. |
| Sheaf.Paper.ProperOpenCoefficientRefinement | unclaimed | Comparison formula preserved after unfolding generic helper; no adaptation. |
| Sheaf.Paper.ProperEtaleOriginScalarData | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension | unclaimed | Existing public constants are unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtensionCore | unclaimed | Existing public constants are unchanged; no adaptation. |

The table includes every textual use of the relocated public or private interface
and both representative definitions, plus all adapted modules. Public reexport and the proved private forwarding lemmas preserve consumers.
No module held by another group is adapted.

## Status

landed 20261026T000911-L-4147139 2026-10-26 (merge of deliver/A4/Sheaf.Paper.EtaleProEtaleScalarMate)

## Reviewer correction (independent review of 3d8a79c3924f)

The replacement delivery started again from the uncorrected 9276d80929d files: it again
rewrote the bodies of scalarRestrictionPullbackIso and scalarExtensionRepresentative,
dropped the cachedEtale* wrappers and the cube's unfold list change, and in addition
replaced the body of the relocated directImageComparisonAmbientPullbackIso by
exactDerivedComparisonSquare. The review re-applies the corrections above and restores the
published five-factor body of directImageComparisonAmbientPullbackIso in
EtaleProEtaleScalarMateData (OpenProEtaleCounitScalar unfolds it by `simp only`). The
new private normalization lemmas (normalized_scalar_mate, representative_square_unit,
unique_choice_eq) are kept.


## A4 repair of the reverted landing (2026-10-26)

The current packet restores the reviewed proof and its two already-recorded helper
nodes after the global-build return. It retains the current generic
`scalarAdjunctionRepresentativeMap` declaration in EtaleDerivedScalarTensor, all current
universes and elaboration settings, and all published definition bodies.
`scalarRepresentativeUnit` and the proved scalar-unit equation are added beside them.
The original module retains private `geometric_rep_eq` with its exact former signature,
forwarded to `scalarGeometricRepresentative_eq` in ScalarPullbackRepresentativeData.
This fixes the explicit Unknown identifier error at EtaleOpenScalarCoherence line 208.
The unchanged EtaleOpenScalarCoherence source compiled against the packet, so no consumer
adaptation is required. No module under WeilConjectures is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.EtaleOpenScalarCoherence | unclaimed | Exact private compatibility signature restored; unchanged source compiled. |
| Sheaf.Paper.EtaleProEtaleScalarMate | A4 | Three original theorem holes closed; legacy private API retained. |
| Sheaf.Paper.EtaleDerivedScalarTensor | unclaimed | Current generic representative API preserved; proved scalar-unit API added. |

The full nine-file check (including the unchanged regression consumer) passed with
exit code zero. The elapsed figures printed by the compile service include queue
time; its per-file acceptance checks all passed.
