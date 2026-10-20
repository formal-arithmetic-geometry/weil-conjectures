module

public import Sheaf.Paper.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Flat
public import Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat
public import Sheaf.SixFunctors.EtaleHomThickLocus

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
/-!
# Canonical étale open tensor and coefficient comparisons

Source: Stacks Tags 0GL1, 0E8I, 06YY, 03EL, 03DI and 0E8J
(blueprint: lem-coef-etale-open-tensor).

The ordinary comparisons are adjunction mates, not arbitrary isomorphisms. The
coefficient comparisons descend their degreewise maps on K-flat representatives.
All derived objects are in the ordinary unbounded constant-coefficient categories.

## Main definitions

* `canonicalGammaZero`, `canonicalGamma`: the ordinary and derived projection maps.
* `openScalarExtension`, `openScalarRestriction`: the fixed natural coefficient comparisons.
* `OpenScalarExtensionNormalization`, `OpenScalarRestrictionNormalization`: their K-flat models.

## Main statements

* `openScalarRestrictionMap_isIso`: invertibility of the fixed scalar/restriction mate.
* `etaleOpenTensorComparisons`: projection, flatness, normalization and coherence laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Exact derived restriction. Source: Stacks 03DJ, 08FJ
(blueprint: lem-coef-etale-open-tensor). -/
abbrev derivedRestriction {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A U :=
  D((j)^*[ModuleCat.{u + 1} A])

/-- Exact derived extension by zero. Source: Stacks 03DJ, 08FJ
(blueprint: lem-coef-etale-open-tensor). -/
abbrev derivedExtension {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategoryModule A U ⥤ DerivedCategoryModule A X :=
  D((j)_!open[ModuleCat.{u + 1} A])

/-- The published canonical open projection map. Source: Stacks 0GL1
(blueprint: lem-coef-etale-open-tensor). -/
def canonicalGamma {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (P : DerivedCategoryModule A U) (T : DerivedCategoryModule A X) :=
  ((derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} A) j).app P).app T

/-- Site flatness in the recorded constant-ring module coordinates. The realization
is the existing constant-module equivalence, not a newly chosen action.
Source: Stacks 03ER (blueprint: lem-coef-etale-open-tensor). -/
abbrev etaleFlat (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) : Prop :=
  SheafOfModules.IsFlatOnSite
    ((Scheme.etaleSumFlatModuleRealization T A).obj P)

/-- The recorded K-flat predicate after the same exact constant-module realization.
Source: Stacks 06YN (blueprint: lem-coef-etale-open-tensor). -/
abbrev etaleKFlat (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    ((Scheme.etaleSumFlatComplexRealization T A).obj P)

/-- Ordinary restriction commutes with restriction of coefficients. The middle
identification is literally the same sectionwise functor. Source: Stacks 03EL, 03EK
(blueprint: lem-coef-etale-open-tensor). -/
def openRestrictScalarsIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (j)^*[ModuleCat.{u + 1} B] ⋙ Sheaf.restrictScalars U.smallEtaleTopology φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙ (j)^*[ModuleCat.{u + 1} A] :=
  Functor.isoWhiskerRight (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j) _ ≪≫
    (show openImmersionRestriction (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars U.smallEtaleTopology φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j from
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) ≪≫
    Functor.isoWhiskerLeft _
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm

/-- Canonical ordinary scalar/restriction comparison `r⁰`, the identification of
left adjoints to sectionwise direct image and restriction of scalars.
Source: Stacks 03EL, 03EK (blueprint: lem-coef-etale-open-tensor). -/
def openScalarRestrictionZero {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (j)^*[ModuleCat.{u + 1} A] ⋙ ProEtale.etaleSheafExtendScalars φ U ≅
      ProEtale.etaleSheafExtendScalars φ X ⋙ (j)^*[ModuleCat.{u + 1} B] :=
  (((ProEtale.etaleSheafExtendScalarsAdjunction φ X).comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)).leftAdjointUniq
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ U)).ofNatIsoRight (Iso.refl _))).symm

/-- Canonical ordinary coefficient/open comparison `q⁰`: uniqueness of left
adjoints to the actual restriction/scalar functors fixes the isomorphism.
Source: Stacks 0E8I, 03DI (blueprint: lem-coef-etale-open-tensor). -/
def openScalarExtensionZero {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (j)_!open[ModuleCat.{u + 1} A] ⋙ ProEtale.etaleSheafExtendScalars φ X ≅
      ProEtale.etaleSheafExtendScalars φ U ⋙ (j)_!open[ModuleCat.{u + 1} B] :=
  ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X)).leftAdjointUniq
    (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).ofNatIsoRight
      (openRestrictScalarsIso φ j))

/-- Exact descent of the canonical restriction/scalar identification.
Source: Stacks 06YY, 08FJ (blueprint: lem-coef-etale-open-tensor). -/
def openDerivedRestrictScalarsIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedRestriction (A := B) j ⋙ Sheaf.derivedRestrictScalars U.smallEtaleTopology φ ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙ derivedRestriction (A := A) j :=
  Functor.mapDerivedCategorySquareIso (openRestrictScalarsIso φ j)

/-- Canonical derived `q`, using the degreewise derived open adjunction and the
published scalar adjunction. Source: Stacks 0E8I, 06YY, 08FJ
(blueprint: lem-coef-etale-open-tensor). -/
def openScalarExtension {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedExtension (A := A) j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ derivedExtension (A := B) j :=
  Adjunction.leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)))
    (((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).ofNatIsoRight
        (openDerivedRestrictScalarsIso φ j))

/-- The canonical scalar/restriction mate, prior to asserting invertibility.
Source: Stacks 03EL, 06YY (blueprint: lem-coef-etale-open-tensor). -/
def openScalarRestrictionMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedRestriction (A := A) j ⋙ scalarExtension φ U ⟶
      scalarExtension φ X ⋙ derivedRestriction (A := B) j :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ))).symm
      (TwoSquare.mk _ _ _ _ (openDerivedRestrictScalarsIso φ j).inv)).natTrans

/-- The canonical mate is invertible for arbitrary coefficient maps.
Source: Stacks 03EL, 06YY (blueprint: lem-coef-etale-open-tensor).
Proof: choose a K-flat flat-term resolution on X. Exact restriction preserves
K-flatness by the open total-tensor identity and the invertible open unit.
Scalar extension is computed on this resolution by ordinary scalar extension.
The displayed mate is then the ordinary balancing isomorphism `r⁰`, as follows
by transposing the sectionwise scalar unit. It is invertible on each resolution,
and hence on every unbounded derived object. -/
@[instance] theorem openScalarRestrictionMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openScalarRestrictionMap φ j) := by
  sorry

/-- The canonical natural isomorphism `r`, with its hom fixed as the specified mate.
Source: Stacks 03EL, 06YY (blueprint: lem-coef-etale-open-tensor). -/
def openScalarRestriction {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedRestriction (A := A) j ⋙ scalarExtension φ U ≅
      scalarExtension φ X ⋙ derivedRestriction (A := B) j :=
  asIso (openScalarRestrictionMap φ j)

/-- The ordinary projection map `γ⁰`, defined as the open-adjunction adjunct
of the unit followed by the canonical restriction/tensor comparison.
Source: Stacks 0E8I, 03EL (blueprint: lem-coef-etale-open-tensor). -/
def canonicalGammaZero
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : Sheaf U.smallEtaleTopology C) (T : Sheaf X.smallEtaleTopology C) :
    (j)_!open[C].obj (P ⊗ (j)^*[C].obj T) ⟶ (j)_!open[C].obj P ⊗ T :=
  ((openImmersionLowerShriekUpperStarAdjunction C j).homEquiv _ _).symm
    ((tensorRightUpperStarIso C j T).hom.app P)

/-- K-flat model normalization of `q`, expressed by the published scalar derived
counits and the exact open localization factors. The bottom chain map is the
ordinary canonical `q⁰` applied degreewise.
Source: Stacks 0E8I, 06YY (blueprint: lem-coef-etale-open-tensor). -/
def OpenScalarExtensionNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (q : derivedExtension (A := A) j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ derivedExtension (A := B) j) : Prop :=
  ∀ P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
    etaleKFlat U A P →
    q.hom.app (_root_.DerivedCategory.Q.obj P) ≫
        (derivedExtension (A := B) j).map (scalarExtensionRepresentative φ U P) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.hom.app
          (((ProEtale.etaleSheafExtendScalars φ U).mapHomologicalComplex (.up ℤ)).obj P) =
      (scalarExtension φ X).map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app P) ≫
        scalarExtensionRepresentative φ X
          (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        _root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (openScalarExtensionZero φ j) (.up ℤ)).hom.app P)

/-- K-flat model normalization of `r`. The bottom map is the canonical ordinary
restriction/balancing map `r⁰`, applied degreewise, not a free iso parameter.
Source: Stacks 03EL, 06YY (blueprint: lem-coef-etale-open-tensor). -/
def OpenScalarRestrictionNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (r : derivedRestriction (A := A) j ⋙ scalarExtension φ U ≅
      scalarExtension φ X ⋙ derivedRestriction (A := B) j) : Prop :=
  ∀ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
    etaleKFlat X A P →
    r.hom.app (_root_.DerivedCategory.Q.obj P) ≫
        (derivedRestriction (A := B) j).map (scalarExtensionRepresentative φ X P) ≫
        (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.hom.app
          (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P) =
      (scalarExtension φ U).map
          ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app P) ≫
        scalarExtensionRepresentative φ U
          (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ≫
        _root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (openScalarRestrictionZero φ j) (.up ℤ)).hom.app P)

section ExactTensor

variable (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Restriction/tensor comparison with exact restriction in both arguments.
Its tensorator is the published K-flat pullback tensor comparison, transported
by the published exact/left-derived restriction identification.
Source: Stacks 03EL, 0GL1 (blueprint: lem-coef-etale-open-tensor). -/
def openExactRestrictionTensor
    (T₁ T₂ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    ((derivedTensor C U).obj (D((j)^*[C]).obj T₁)).obj (D((j)^*[C]).obj T₂) ≅
      D((j)^*[C]).obj (((derivedTensor C X).obj T₁).obj T₂) :=
  ((derivedTensor C U).obj (D((j)^*[C]).obj T₁)).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory C j).app T₂).symm ≪≫
    ((mapDerivedCategoryUpperStarDerivedTensorIso C j).app T₁).app T₂

/-- The canonical projection map written with exact `j^*`. The change from
`Lj^*` is the existing exact/left-derived comparison, not a new derived functor.
Source: Stacks 0GL1 (blueprint: lem-coef-etale-open-tensor). -/
def canonicalGammaExact
    (P : _root_.DerivedCategory (Sheaf U.smallEtaleTopology C))
    (T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    D((j)_!open[C]).obj (((derivedTensor C U).obj P).obj (D((j)^*[C]).obj T)) ⟶
      ((derivedTensor C X).obj (D((j)_!open[C]).obj P)).obj T :=
  D((j)_!open[C]).map
      (((derivedTensor C U).obj P).map
        ((leftDerivedUpperStarIsoMapDerivedCategory C j).inv.app T)) ≫
    ((derivedOpenImmersionLowerShriekProjectionMap C j).app P).app T

end ExactTensor

/-- The full open tensor/coefficient assertion. Every comparison in these laws is
fixed above, or is a published canonical scalar tensor/composition comparison.
Source: Stacks 0GL1, 0E8I, 06YY, 03EL, 03DI, 0E8J
(blueprint: lem-coef-etale-open-tensor). -/
structure EtaleOpenTensorComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Prop where
  gamma_isIso : ∀ (P : DerivedCategoryModule A U) (T : DerivedCategoryModule A X),
    IsIso (canonicalGamma j P T)
  ordinary_tensor : ∀ (P : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (T : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
    IsIso (canonicalGammaZero (ModuleCat.{u + 1} A) j P T)
  flat_preserved : ∀ P : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
    etaleFlat U A P → etaleFlat X A ((j)_!open[ModuleCat.{u + 1} A].obj P)
  kflat_preserved : ∀ P : CochainComplex
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
    etaleKFlat U A P → etaleKFlat X A
      (((j)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj P)
  q_normalized : OpenScalarExtensionNormalization φ j (openScalarExtension φ j)
  q_unique : ∀ q : derivedExtension (A := A) j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ derivedExtension (A := B) j,
    OpenScalarExtensionNormalization φ j q → q = openScalarExtension φ j
  r_normalized : OpenScalarRestrictionNormalization φ j (openScalarRestriction φ j)
  r_unique : ∀ r : derivedRestriction (A := A) j ⋙ scalarExtension φ U ≅
      scalarExtension φ X ⋙ derivedRestriction (A := B) j,
    OpenScalarRestrictionNormalization φ j r → r = openScalarRestriction φ j
  q_restricts : ∀ P : DerivedCategoryModule A U,
    (derivedRestriction (A := B) j).map ((openScalarExtension φ j).hom.app P) ≫
        (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).unit.app _)).inv =
      (openScalarRestriction φ j).inv.app ((derivedExtension (A := A) j).obj P) ≫
        (scalarExtension φ U).map
          (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).unit.app P)).inv
  counit : ∀ T : DerivedCategoryModule A X,
    (openScalarExtension φ j).hom.app ((derivedRestriction (A := A) j).obj T) ≫
        (derivedExtension (A := B) j).map ((openScalarRestriction φ j).hom.app T) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).counit.app ((scalarExtension φ X).obj T) =
      (scalarExtension φ X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app T)
  tensor_associative : ∀ (P : DerivedCategoryModule A U)
      (T₁ T₂ : DerivedCategoryModule A X),
    (derivedExtension (A := A) j).map
        ((derivedTensorAssociator (ModuleCat.{u + 1} A) U P
            ((derivedRestriction j).obj T₁) ((derivedRestriction j).obj T₂)).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} A) U).obj P).map
            (openExactRestrictionTensor (ModuleCat.{u + 1} A) j T₁ T₂).hom) ≫
        canonicalGammaExact (ModuleCat.{u + 1} A) j P
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj T₁).obj T₂) =
      canonicalGammaExact (ModuleCat.{u + 1} A) j
          (((derivedTensor (ModuleCat.{u + 1} A) U).obj P).obj
            ((derivedRestriction j).obj T₁)) T₂ ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).map
          (canonicalGammaExact (ModuleCat.{u + 1} A) j P T₁)).app T₂ ≫
        (derivedTensorAssociator (ModuleCat.{u + 1} A) X
          ((derivedExtension j).obj P) T₁ T₂).hom
  successive_scalar : ∀ {C : Type (u + 1)} [CommRing C] (ψ : B →+* C)
      (P : DerivedCategoryModule A U),
    (scalarExtension ψ X).map ((openScalarExtension φ j).hom.app P) ≫
        (openScalarExtension ψ j).hom.app ((scalarExtension φ U).obj P) ≫
        (derivedExtension (A := C) j).map
          ((ProEtale.pbcFixedScalarExtensionComp U.smallEtaleTopology φ ψ
            (ψ.comp φ) rfl).hom.app P) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app ((derivedExtension (A := A) j).obj P) ≫
        (openScalarExtension (ψ.comp φ) j).hom.app P
  mixed_tensor_scalar : ∀ (P : DerivedCategoryModule A U) (T : DerivedCategoryModule A X),
    canonicalGammaExact (ModuleCat.{u + 1} B) j
        ((scalarExtension φ U).obj P) ((scalarExtension φ X).obj T) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) X).map
          ((openScalarExtension φ j).inv.app P)).app ((scalarExtension φ X).obj T) ≫
        (etaleHomTensorComparison X φ ((derivedExtension (A := A) j).obj P) T).hom =
      (derivedExtension (A := B) j).map
          (((derivedTensor (ModuleCat.{u + 1} B) U).obj ((scalarExtension φ U).obj P)).map
              ((openScalarRestriction φ j).inv.app T) ≫
            (etaleHomTensorComparison U φ P ((derivedRestriction j).obj T)).hom) ≫
        (openScalarExtension φ j).inv.app
          (((derivedTensor (ModuleCat.{u + 1} A) U).obj P).obj ((derivedRestriction j).obj T)) ≫
        (scalarExtension φ X).map (canonicalGammaExact (ModuleCat.{u + 1} A) j P T)

/-- The canonical open comparisons obey the projection, K-flat normalization,
open counit, associativity, scalar-tower and mixed tensor/scalar laws.
Source: Stacks 0GL1, 0E8I, 06YY, 03EL, 03DI, 0E8J
(blueprint: lem-coef-etale-open-tensor).

Proof: (1) Localize the small étale site at the open object. The ordinary
adjunction has sectionwise identity unit on U and the specified counit summand
formula. (2) Transpose the unit tensored with restriction. This gives `γ⁰`,
whose restriction is the identity; both sides have open support, so it is an
isomorphism. (3) Tensoring a short exact sequence, restricting, and applying
exact extension by zero proves preservation of flat sheaves. Applying the same
isomorphism to every bidegree of direct-sum total tensor proves preservation of
K-flat complexes. Restriction also preserves K-flatness: test with an acyclic
complex on U, extend by zero, and restrict back using the invertible unit.
(4) The exact open adjunction descends degreewise; its units and counits are
those of the published derived adjunction. A K-flat resolution computes the
published `canonicalGamma`, proving invertibility without boundedness.
(5) Specialize inverse ordinary projection to the coefficient sheaf B; its
pure-tensor formula is j_!p tensor b maps to j_!(p tensor b). The scalar
adjunction shows it is precisely `openScalarExtensionZero`. Restriction of
ordinary balancing is `openScalarRestrictionZero`. Apply both degreewise to
K-flat models. The exact localization factors and published scalar counits give
the two normalization equations. Every derived object has a K-flat resolution;
naturality on that resolution determines each component, proving uniqueness.
(6) On the same models the restriction identity and counit equation send every
extension-presheaf tensor generator to the same section. Sheafification and
localization give the displayed equalities. (7) Rebracket triple total tensors:
the differential signs on both sides are 1, (-1)^p and (-1)^(p+q). Both paths
of `tensor_associative` send the same local tensor generator to the same tensor.
(8) In a tower A to B to C the canonical composition comparison multiplies
coefficients, ((p tensor b) tensor c) maps to p tensor bc. Applying q directly
or successively gives the same result. (9) The mixed square uses the published
uniquely normalized strong scalar tensor comparison, sending
(p tensor b₁) tensor (t tensor b₂) to (p tensor t) tensor b₁b₂.
Either path commutes with the open projection on these generators. Descend all
three equalities using the K-flat model comparisons. The argument applies to
arbitrary coefficient maps and unbounded complexes. -/
theorem etaleOpenTensorComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    EtaleOpenTensorComparisons φ j := by
  sorry

end AlgebraicGeometry.Etale
