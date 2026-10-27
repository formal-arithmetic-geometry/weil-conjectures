module

public import Sheaf.CategoryTheory.RingedSiteModuleCupProduct
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.AlgebraicGeometry.AbelianAffineReducedCoproduct
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.RingTheory.Localization.Away.Basic


import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.CategoryTheory.GlobalModuleAbelianCohomology
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.AlgebraicGeometry.SpaceAffineDerivedProjectionFormula
import Sheaf.Paper.RingedProjectionTensorComposition
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.RingTheory.Flat.Localization
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Projective coherent cohomology and arbitrary coefficients

Source: Stacks Project, Tags 08IN, 08IR, 0FPL, 0FPM and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.AlgebraicSpace.ProjectiveKunneth

variable {S : Scheme.{u}}

/-- The existing small ringed site, with its native localization tensor.
Source: Stacks 03ED, 039Z and 06YT
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def corner (X : AlgebraicSpace S) [HasDerivedCategory.{u} X.SmallModules] :
    RingedTensorCorner.{u, u} where
  site := X.SmallEtaleModel
  topology := X.smallEtaleModelTopology
  ring := X.smallStructureSheaf
  tensor := @tensor (DerivedCategory.{u} X.SmallModules) _
    (CategoryTheory.RingedDerivedNative.monoidal.{u, u, u, u}
      X.smallEtaleModelTopology X.smallStructureSheaf)

/-- Additive-sheaf cohomology on the affine basis of the small etale site.
Source: Stacks 039Z and 03FD
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def H (R : Type u) [CommRing R] (T : Over S) (_e : T.left ≅ Spec (.of R))
    (X : AlgebraicSpace S) (_f : X ⟶ schemeSpace T) (F : X.SmallModules) (n : ℕ) :
    AddCommGrpCat.{u} :=
  ((Sheaf.Γ X.smallEtaleModelTopology AddCommGrpCat.{u}).rightDerived n).obj
    ((SheafOfModules.toSheaf X.smallStructureRings).obj F)

/-- The actual structural R-action, restricted from the canonical global-function action.
Source: Stacks 03FD and 08IN
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
instance moduleH (R : Type u) [CommRing R] (T : Over S) (e : T.left ≅ Spec (.of R))
    (X : AlgebraicSpace S) [HasDerivedCategory.{u} X.SmallModules]
    (f : X ⟶ schemeSpace T) (F : X.SmallModules) (n : ℕ) :
    Module R (H R T e X f F n) :=
  letI : Module (RingCat.sectionsSubring X.smallStructureRings.obj)
      (H R T e X f F n) :=
    SheafOfModules.RingedSiteCup.globalCohomologyModule (corner X) F n
  Module.compHom (H R T e X f F n) (affineGlobalScalar R T e X f)

variable [∀ X : AlgebraicSpace S, HasDerivedCategory.{u} X.SmallModules]

/-- Structure-module coefficients.
Source: Stacks 08IN (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
abbrev O (X : AlgebraicSpace S) := SheafOfModules.unit X.smallStructureRings

/-- The map of the actual additive-sheaf cohomology groups.
Source: Stacks 03FD (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def mapH (X : AlgebraicSpace S) {F G : X.SmallModules} (a : F ⟶ G) (n : ℕ) :=
  ((Sheaf.Γ X.smallEtaleModelTopology AddCommGrpCat.{u}).rightDerived n).map
    ((SheafOfModules.toSheaf X.smallStructureRings).map a)

section Affine
variable (R : Type u) [CommRing R] (T : Over S) (e : T.left ≅ Spec (.of R))
  (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)

/-- Global functions act through the actual structural scalar map.
Source: Stacks 08IN (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
abbrev scalarRestriction : ModuleCat.{u} (RingCat.sectionsSubring X.smallStructureRings.obj) ⥤
    ModuleCat.{u} R := ModuleCat.restrictScalars.{u} (affineGlobalScalar R T e X f)

/-- Exact scalar restriction preserves finite limits, detected on additive groups.
Source: Stacks 03FD (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
instance scalarRestriction_limits : PreservesFiniteLimits (scalarRestriction R T e X f) :=
  ⟨fun _J _ _ => ⟨fun {F} => ModuleCat.preservesLimit_restrictScalars _ F⟩⟩

/-- Exact scalar restriction preserves finite colimits, detected on additive groups.
Source: Stacks 03FD (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
instance scalarRestriction_colimits : PreservesFiniteColimits (scalarRestriction R T e X f) :=
  preservesFiniteColimits_of_reflects_of_preserves (scalarRestriction R T e X f)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-- Compatible-section normalization of the affine global-sections comparison.
Source: Stacks 039Z and 03FD
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def SectionsComparisonNormalized
    (c : SheafOfModules.RingedSiteCup.globalSections (corner X) ⋙
      scalarRestriction R T e X f ≅ spaceAffineSections T e f) : Prop :=
  ∀ (F : X.SmallModules)
    (s : (SheafOfModules.RingedSiteCup.globalSections (corner X)).obj F)
    (U : X.EtaleSite),
    spaceAffineSectionAt T e f F U ((c.hom.app F) s) =
      (fullModuleSection X F s).val.app (op U) (1 : X.structureSheaf.obj.obj (op U))

/-- The unique compatible-section comparison with the published geometric sections functor.
Source: Stacks 039Z, 03FD and 03G8
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: a map O to F is the compatible family of its values on 1. Extend it by the
recorded affine-basis equivalence. The direct-image chart projections defining
spaceAffineSections recover that family; conversely these projections give a
map from O. The two constructions are inverse, R-linear by the structural chart
formula, and natural in F. Chart projections jointly detect equality, giving uniqueness. -/
theorem sectionsComparison_existsUnique :
    ∃! c, SectionsComparisonNormalized R T e X f c := by
  sorry

/-- The comparison determined by the actual compatible families.
Source: Stacks 03FD (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def sectionsComparison := (sectionsComparison_existsUnique R T e X f).choose

/-- Its canonical derived comparison, using exact restriction of scalar coefficients.
Source: Stacks 03FD and 070K
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def derivedSectionsComparison :
    SheafOfModules.RingedSiteCup.derivedGlobalSections (corner X) ⋙
        (scalarRestriction R T e X f).mapDerivedCategory ≅
      spaceAffineDerivedSections T e f := by
  letI := scalarRestriction_limits R T e X f
  letI := scalarRestriction_colimits R T e X f
  letI := spaceAffineSections_additive T e f
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (SheafOfModules.RingedSiteCup.globalSections (corner X))
    (scalarRestriction R T e X f)).symm ≪≫
      Functor.rightDerivedFunctorNatIso (sectionsComparison R T e X f)

/-- The underlying additive cohomology is identified with the existing R-valued RΓ.
Source: Stacks 03FD (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def cohomologyComparison (F : X.SmallModules) (n : ℕ) :
    H R T e X f F n ≃+
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
        ((spaceAffineDerivedSections T e f).obj
          ((DerivedCategory.singleFunctor X.SmallModules 0).obj F)) :=
  (SheafOfModules.RingedSiteCup.globalCohomologyLinearEquiv (corner X) F n).toAddEquiv.trans
    (((scalarRestriction R T e X f).mapDerivedCategoryHomologyFunctorIso (n : ℤ)).app
      ((SheafOfModules.RingedSiteCup.derivedGlobalSections (corner X)).obj
        ((DerivedCategory.singleFunctor X.SmallModules 0).obj F))).toLinearEquiv.toAddEquiv
      |>.trans ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).mapIso
        ((derivedSectionsComparison R T e X f).app
          ((DerivedCategory.singleFunctor X.SmallModules 0).obj F))).toLinearEquiv.toAddEquiv

/-- The universal left-derived counit on an ordinary sheaf in degree zero.
Source: Stacks 06YY (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def pullbackSingleCounit {Y : AlgebraicSpace S} (h : X ⟶ Y) (F : Y.SmallModules) :
    (spaceDerivedPullback h).obj ((DerivedCategory.singleFunctor Y.SmallModules 0).obj F) ⟶
      (DerivedCategory.singleFunctor X.SmallModules 0).obj
        ((smallModuleTensorPullback h).obj F) :=
  (spaceDerivedPullback h).map ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app F) ≫
    (spaceDerivedPullbackCounit h).app
      ((HomologicalComplex.single Y.SmallModules (.up ℤ) 0).obj F) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (smallModuleTensorPullback h) (.up ℤ) 0).hom.app F) ≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app _

/-- The canonical global pullback, including coefficient evaluation, before taking homology.
Source: Stacks 06YY and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def derivedPullback
    {B : Type u} [CommRing B] {T' : Over S} (e' : T'.left ≅ Spec (.of B))
    (g : T' ⟶ T) {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (f' : Y ⟶ schemeSpace T')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace T' ⟶ schemeSpace T))
    (F : X.SmallModules) (G : Y.SmallModules)
    (a : (smallModuleTensorPullback h).obj F ⟶ G) :
    (spaceAffineDerivedSections T e f).obj
        ((DerivedCategory.singleFunctor X.SmallModules 0).obj F) ⟶
      (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g)).obj
        ((spaceAffineDerivedSections T' e' f').obj
          ((DerivedCategory.singleFunctor Y.SmallModules 0).obj G)) :=
  (spaceAffineDerivedSections T e f).map
      ((spaceDerivedAdjunction h).unit.app
        ((DerivedCategory.singleFunctor X.SmallModules 0).obj F)) ≫
    (spaceDerivedSectionsComposition e e' g f h f' sq).hom.app
      ((spaceDerivedPullback h).obj
        ((DerivedCategory.singleFunctor X.SmallModules 0).obj F)) ≫
    (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g)).map
      ((spaceAffineDerivedSections T' e' f').map
        (pullbackSingleCounit Y h F ≫
          (DerivedCategory.singleFunctor Y.SmallModules 0).map a))

/-- Additive-sheaf pullback, through the canonical RΓ comparison, for arbitrary h.
Source: Stacks 03FD, 06YY and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def pullbackH
    {B : Type u} [CommRing B] {T' : Over S} (e' : T'.left ≅ Spec (.of B))
    (g : T' ⟶ T) {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (f' : Y ⟶ schemeSpace T')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace T' ⟶ schemeSpace T))
    (F : X.SmallModules) (G : Y.SmallModules)
    (a : (smallModuleTensorPullback h).obj F ⟶ G) (n : ℕ) :
    H R T e X f F n →+ H B T' e' Y f' G n :=
  (cohomologyComparison B T' e' Y f' G n).symm.toAddMonoidHom.comp
    (((Functor.mapDerivedCategoryHomologyFunctorIso
      (ModuleCat.restrictScalars (spaceAffineRingMap e e' g)) (n : ℤ)).inv.app
        ((spaceAffineDerivedSections T' e' f').obj
          ((DerivedCategory.singleFunctor Y.SmallModules 0).obj G))).hom.toAddMonoidHom.comp
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (derivedPullback R T e X f e' g h f' sq F G a)).hom.toAddMonoidHom.comp
          (cohomologyComparison R T e X f F n).toAddMonoidHom))

end Affine

/-- Restrict the native tensorator to the flat K-flat representatives required by cup.
Source: Stacks 06YT (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def tensorModel (X : AlgebraicSpace S) : RingedTensorModel (corner X) where
  representative := Functor.isoWhiskerLeft
    (({
      obj := fun P ↦ ⟨P.obj,
        (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
      map := fun a ↦ ObjectProperty.homMk a.hom } :
      ObjectProperty.FullSubcategory (corner X).mateFlat ⥤
        ObjectProperty.FullSubcategory
          (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
            (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf))).prod
    ({
      obj := fun P ↦ ⟨P.obj,
        (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
      map := fun a ↦ ObjectProperty.homMk a.hom } :
      ObjectProperty.FullSubcategory (corner X).mateFlat ⥤
        ObjectProperty.FullSubcategory
          (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
            (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf))))
    (CategoryTheory.RingedDerivedNative.comparison.{u, u, u, u}
      X.smallEtaleModelTopology X.smallStructureSheaf)

/-- Cup with coefficient multiplication, using exactly the recorded global cup.
Source: Stacks 0B6C (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def cup (R : Type u) [CommRing R] (T : Over S) (e : T.left ≅ Spec (.of R))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)
    (F G K : X.SmallModules) (m : F ⊗ G ⟶ K) (i j : ℕ)
    (a : H R T e X f F i) (b : H R T e X f G j) : H R T e X f K (i + j) :=
  SheafOfModules.RingedSiteCup.globalCupWith (corner X) (tensorModel X) F G K m i j a b

/-- The canonical degree-zero class of a global module section.
Source: Stacks 03FD (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def sectionClass (R : Type u) [CommRing R] (T : Over S) (e : T.left ≅ Spec (.of R))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T) (F : X.SmallModules)
    (s : O X ⟶ F) : H R T e X f F 0 :=
  ((Sheaf.Γ X.smallEtaleModelTopology AddCommGrpCat.{u}).toRightDerivedZero.app
    ((SheafOfModules.toSheaf X.smallStructureRings).obj F))
      ((SheafOfModules.RingedSiteCup.globalUnderlyingSections (corner X)).hom.app F s)

/-- Transport only the degree, without changing the class.
Source: Stacks 0B6C (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def castH (R : Type u) [CommRing R] (T : Over S) (e : T.left ≅ Spec (.of R))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T) (F : X.SmallModules)
    {i j : ℕ} (h : i = j) (a : H R T e X f F i) : H R T e X f F j := h ▸ a

section Coefficients
variable (R : Type u) [CommRing R] (T : Over S) (e : T.left ≅ Spec (.of R))
  (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)

/-- Ordinary quasi-coherent scalar-extension coefficients, with no flatness condition on N.
Source: Stacks 03EL (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
abbrev coefficients (N : ModuleCat.{u} R) : X.SmallModules :=
  (affineScalarPullback R T e X f).obj N

/-- The canonical coefficient map is determined on every pure tensor by 1 mapping to 1⊗n.
Source: Stacks 08IN and 0B6C
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: the adjunction unit is R-linear in n. Cohomology is additive and respects the
structural R-action. Thus (a,n) maps to H(1 maps to 1 tensor n)(a) is R-bilinear.
The tensor universal property gives the unique linear map, independently of any splitting.
-/
theorem alpha_existsUnique (N : ModuleCat.{u} R) (n : ℕ) :
    ∃! α : (H R T e X f (O X) n ⊗[R] N) →ₗ[R]
        H R T e X f (coefficients R T e X f N) n,
      ∀ (a : H R T e X f (O X) n) (v : N),
        α (a ⊗ₜ[R] v) = mapH X ((affineScalarAdjunction R T e X f).unit.app N v) n a := by
  sorry

/-- The actual canonical coefficient map, uniquely fixed by all pure tensors.
Source: Stacks 08IN (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def alpha (N : ModuleCat.{u} R) (n : ℕ) :
    (H R T e X f (O X) n ⊗[R] N) →ₗ[R]
      H R T e X f (coefficients R T e X f N) n :=
  (alpha_existsUnique R T e X f N n).choose

/-- Canonical structure-sheaf pullback for every morphism over the affine base.
Source: Stacks 06YY and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def structurePullback {Y : AlgebraicSpace S} (g : Y ⟶ schemeSpace T)
    (h : Y ⟶ X) (w : h ≫ f = g) (n : ℕ) :
    H R T e X f (O X) n →+ H R T e Y g (O Y) n :=
  pullbackH R T e X f e (𝟙 T) h g (by change h ≫ f = g ≫ 𝟙 _; simpa using w)
    (O X) (O Y) (Poincare.pullbackUnit h).hom n

/-- Canonical coefficient pullback for every morphism, with the normalized sheaf comparison.
Source: Stacks 03EL, 06YY and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def coefficientPullback {Y : AlgebraicSpace S} (g : Y ⟶ schemeSpace T)
    (h : Y ⟶ X) (w : h ≫ f = g) (N : ModuleCat.{u} R) (n : ℕ) :
    H R T e X f (coefficients R T e X f N) n →+
      H R T e Y g (coefficients R T e Y g N) n :=
  pullbackH R T e X f e (𝟙 T) h g (by change h ≫ f = g ≫ 𝟙 _; simpa using w)
    (coefficients R T e X f N) (coefficients R T e Y g N)
    ((ReducedCoproduct.coefficientComparison R T e f h g w).hom.app N) n

/-- Multiplication of structure-sheaf cohomology is the existing global cup and unitor.
Source: Stacks 0B6C (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def multiply (i j : ℕ) (a : H R T e X f (O X) i) (b : H R T e X f (O X) j) :
    H R T e X f (O X) (i + j) :=
  cup R T e X f (O X) (O X) (O X) (λ_ (O X)).hom i j a b

end Coefficients

section Product
variable (R : Type u) [CommRing R] (T : Over S) (e : T.left ≅ Spec (.of R))
  {X Y : AlgebraicSpace S} (f : X ⟶ schemeSpace T) (g : Y ⟶ schemeSpace T)

/-- The actual structural map of the fibre product.
Source: Stacks 02X2 (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def productMap : Poincare.product f g ⟶ schemeSpace T := Poincare.fst f g ≫ f

/-- The second projection has the same structural composite.
Source: Stacks 02X2 (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: this is the pullback cone's commuting square, transported to the full subcategory. -/
theorem productMap_snd : Poincare.snd f g ≫ g = productMap T f g := by
  sorry

/-- The degree n summand of the tensor of the two nonnegative cohomology gradings.
Source: Stacks 0FPJ (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
abbrev summands (n : ℕ) :=
  ⨁ d : {d : ℕ × ℕ // d.1 + d.2 = n},
    H R T e X f (O X) d.val.1 ⊗[R] H R T e Y g (O Y) d.val.2

/-- Inclusion of a pure homogeneous tensor, with its displayed total degree.
Source: Stacks 0FPJ (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def includeTensor (i j : ℕ) (a : H R T e X f (O X) i) (b : H R T e Y g (O Y) j) :
    summands R T e f g (i + j) :=
  DirectSum.lof R {d : ℕ × ℕ // d.1 + d.2 = i + j}
    (fun d => H R T e X f (O X) d.val.1 ⊗[R] H R T e Y g (O Y) d.val.2)
      ⟨(i, j), rfl⟩ (a ⊗ₜ[R] b)

/-- The actual external cup class, before the coefficient map.
Source: Stacks 08IR and 0FPJ
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def external (i j : ℕ) (a : H R T e X f (O X) i) (b : H R T e Y g (O Y) j) :
    H R T e (Poincare.product f g) (productMap T f g) (O (Poincare.product f g)) (i + j) :=
  multiply R T e _ (productMap T f g) i j
    (structurePullback R T e X f (productMap T f g) (Poincare.fst f g) rfl i a)
    (structurePullback R T e Y g (productMap T f g) (Poincare.snd f g)
      (productMap_snd T f g) j b)

/-- The unique linear external cup with arbitrary coefficients.
Source: Stacks 08IN, 08IR and 0FPJ
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: pullback is R-linear, cup is R-bilinear, and alpha is R-linear on the tensor.
Their composite on each summand is bilinear in a,b and then in the coefficient.
The tensor and direct-sum universal properties give existence and uniqueness. -/
theorem kappa_existsUnique (N : ModuleCat.{u} R) (n : ℕ) :
    ∃! κ : (summands R T e f g n ⊗[R] N) →ₗ[R]
        H R T e (Poincare.product f g) (productMap T f g)
          (coefficients R T e _ (productMap T f g) N) n,
      ∀ (i j : ℕ) (h : i + j = n)
        (a : H R T e X f (O X) i) (b : H R T e Y g (O Y) j) (v : N),
        κ ((h ▸ includeTensor R T e f g i j a b) ⊗ₜ[R] v) =
          alpha R T e _ (productMap T f g) N n
            (castH R T e _ (productMap T f g) (O _) h (external R T e f g i j a b) ⊗ₜ[R] v) := by
  sorry

/-- The canonical external cup map, fixed by the pure-generator formula.
Source: Stacks 08IN and 08IR
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def kappa (N : ModuleCat.{u} R) (n : ℕ) :
    (summands R T e f g n ⊗[R] N) →ₗ[R]
      H R T e (Poincare.product f g) (productMap T f g)
        (coefficients R T e _ (productMap T f g) N) n :=
  (kappa_existsUnique R T e f g N n).choose

/-- The coefficient-R external cup, using the canonical identification O tensor_R R=O.
Source: Stacks 08IR and 0FPJ
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: R-linearity of pullback and bilinearity of cup descend through each tensor,
then the direct-sum universal property gives the unique map with these values. -/
theorem kappaStructure_existsUnique (n : ℕ) :
    ∃! κ : summands R T e f g n →ₗ[R]
        H R T e (Poincare.product f g) (productMap T f g) (O _) n,
      ∀ (i j : ℕ) (h : i + j = n)
        (a : H R T e X f (O X) i) (b : H R T e Y g (O Y) j),
        κ (h ▸ includeTensor R T e f g i j a b) =
          castH R T e _ (productMap T f g) (O _) h (external R T e f g i j a b) := by
  sorry

/-- The homogeneous degree of the graded-algebra external cup.
Source: Stacks 08IR (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def kappaStructure (n : ℕ) : summands R T e f g n →ₗ[R]
    H R T e (Poincare.product f g) (productMap T f g) (O _) n :=
  (kappaStructure_existsUnique R T e f g n).choose

/-- The coefficient map preserves the canonical R-coefficient identification.
Source: Stacks 08IN and 03EL
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: the scalar extension of R is the unit, by multiplication. On generators,
the coefficient-R formula reduces to scalar multiplication; the tensor and direct-sum
universal properties give the identity for every source element. -/
theorem kappa_structure_coefficients (n : ℕ) (x : summands R T e f g n) :
    kappa R T e f g (ModuleCat.of R R) n (x ⊗ₜ[R] (1 : R)) =
      alpha R T e _ (productMap T f g) (ModuleCat.of R R) n
        (kappaStructure R T e f g n x ⊗ₜ[R] (1 : R)) := by
  sorry

/-- Coefficient Kunneth for flat qcqs spaces with finite projective bounded cohomology.
Source: Stacks 08IN, 08IR; finite-projective specialization in the DAG's ten-step proof
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof:
1. Flatness, quasi-compactness and quasi-separatedness persist under products and localization.
2. The ringed-site module/abelian comparison identifies C_Z=RGamma(O_Z) with H used here.
The flat-space derived external cup gives C_X tensor-derived C_Y isomorphic to C_P.
3. Lift every projective cohomology group into cycles, obtaining a bounded zero-differential
complex quasi-isomorphic to C_Z. These choices verify invertibility only.
4. Projective terms are flat; bounded flat complexes are K-flat. The total tensor of the
zero-differential models has degree n the displayed finite direct sum. Cocycle normalization
identifies its comparison with the actual external cup. Product cohomology is finite projective.
5. The flat affine derived projection formula identifies C_Z tensor-derived N with RGamma(N_Z),
for arbitrary N. Flatness of Z over R makes this the ordinary coefficient sheaf.
6. The same K-flat model computes its cohomology as H_Z tensor N. Naturality for R to N,
1 to v, and the projection unit identify the arrow with alpha on every pure tensor.
7. Kappa factors as the external-cup isomorphism tensored with N followed by alpha_P.
Tensor preserves an isomorphism without requiring exactness of tensoring by N.
8. Naturality follows from the adjunction units, tensor counits and their pasting identities.
9. Apply flat base change to R_s, retaining the same pure-section and cocycle formulas.
10. Koszul symmetry gives the graded commutativity and signed multiplication formula.
-/
theorem projective_cohomology_coefficient_kunneth
    (hf : MapIsFlat f) (hg : MapIsFlat g)
    (hfc : MapIsQuasiCompact f.hom.hom) (hgc : MapIsQuasiCompact g.hom.hom)
    (hfs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (hgs : MapIsQuasiCompact (pullback.diagonal g.hom.hom))
    (hX : ∀ i : ℕ, Module.Finite R (H R T e X f (O X) i) ∧
      Module.Projective R (H R T e X f (O X) i))
    (hY : ∀ i : ℕ, Module.Finite R (H R T e Y g (O Y) i) ∧
      Module.Projective R (H R T e Y g (O Y) i))
    (bX : ∃ b : ℕ, ∀ i : ℕ, b < i → Subsingleton (H R T e X f (O X) i))
    (bY : ∃ b : ℕ, ∀ i : ℕ, b < i → Subsingleton (H R T e Y g (O Y) i)) :
    ∀ (N : ModuleCat.{u} R) (n : ℕ),
      Function.Bijective (alpha R T e X f N n) ∧
      Function.Bijective (alpha R T e Y g N n) ∧
      Function.Bijective (alpha R T e _ (productMap T f g) N n) ∧
      Function.Bijective (kappa R T e f g N n) ∧
      Function.Bijective (kappaStructure R T e f g n) := by
  sorry

/-- The Kunneth product has exactly the Koszul sign on the crossed middle factors.
Together with homogeneous bijectivity and the unit formula, this is the graded-algebra
isomorphism assertion: pure homogeneous tensors generate the source graded algebra.
Source: Stacks 0FPL, 0FPM and 08IR
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: expand the two external cups. Associate the four pulled classes, interchange
b and c using graded commutativity, and regroup using multiplicativity of pullback.
This gives (-1)^(j*k) times the external cup of ac and bd. All operations are bilinear,
so the generator formula determines the product on the whole direct sum. Units pull
back to units and their cup is the unit, giving the second formula. -/
theorem external_signed_product (i j k l : ℕ)
    (a : H R T e X f (O X) i) (b : H R T e Y g (O Y) j)
    (c : H R T e X f (O X) k) (d : H R T e Y g (O Y) l) :
    castH R T e _ (productMap T f g) (O _)
      (by simp only [Nat.add_assoc, Nat.add_left_comm] :
        (i + j) + (k + l) = (i + k) + (j + l))
      (multiply R T e _ (productMap T f g) (i + j) (k + l)
        (external R T e f g i j a b) (external R T e f g k l c d)) =
      ((-1 : R) ^ (j * k)) • external R T e f g (i + k) (j + l)
        (multiply R T e X f i k a c) (multiply R T e Y g j l b d) := by
  sorry

/-- The external cup carries the tensor of the two units to the product-space unit.
Source: Stacks 0FPJ and 08IR
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: both projections preserve the unit; the unit identity for cup gives the formula. -/
theorem external_unit :
    external R T e f g 0 0 (sectionClass R T e X f (O X) (𝟙 _))
      (sectionClass R T e Y g (O Y) (𝟙 _)) =
      sectionClass R T e _ (productMap T f g) (O _) (𝟙 _) := by
  sorry

/-- External cup is natural in every coefficient module map, without an exactness condition.
Source: Stacks 08IN and 08IR
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: on each generator this is naturality of alpha for the same external cup class.
The tensor and direct-sum generators determine both maps on every element. -/
theorem kappa_natural (N M : ModuleCat.{u} R) (a : N ⟶ M) (n : ℕ)
    (x : summands R T e f g n ⊗[R] N) :
    mapH _ ((affineScalarPullback R T e _ (productMap T f g)).map a) n
        (kappa R T e f g N n x) =
      kappa R T e f g M n (TensorProduct.map LinearMap.id a.hom x) := by
  sorry

end Product

section Laws
variable (R : Type u) [CommRing R] (T : Over S) (e : T.left ≅ Spec (.of R))
  (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)

/-- Alpha is cup with precisely the section 1 tensor v, rather than a chosen splitting.
Source: Stacks 0B6C and 08IN
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: the adjoint of cup with a degree-zero section is the tensor of the counit
with that section. The unit triangle cancels the extra unit, giving the coefficient
sheaf map 1 maps to 1 tensor v. Apply cohomology and the defining alpha formula. -/
theorem alpha_cup (N : ModuleCat.{u} R) (n : ℕ)
    (a : H R T e X f (O X) n) (v : N) :
    alpha R T e X f N n (a ⊗ₜ[R] v) =
      castH R T e X f (coefficients R T e X f N) (Nat.add_zero n)
        (cup R T e X f (O X) (coefficients R T e X f N)
          (coefficients R T e X f N) (λ_ _).hom n 0 a
          (sectionClass R T e X f _ ((affineScalarAdjunction R T e X f).unit.app N v))) := by
  sorry

/-- Alpha is natural for every R-linear coefficient homomorphism.
Source: Stacks 08IN and 0B6C
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: the scalar-adjunction unit is natural in the module. Its square gives the
identity on a tensor v; tensor generation and additivity give it for arbitrary x. -/
theorem alpha_natural (N M : ModuleCat.{u} R) (a : N ⟶ M) (n : ℕ)
    (x : H R T e X f (O X) n ⊗[R] N) :
    mapH X ((affineScalarPullback R T e X f).map a) n (alpha R T e X f N n x) =
      alpha R T e X f M n (TensorProduct.map LinearMap.id a.hom x) := by
  sorry

/-- Arbitrary geometric pullback is R-linear on structure and coefficient cohomology.
Source: Stacks 06YY and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: the derived adjunction unit and global-sections composition are R-linear;
the structural and scalar-extension comparisons retain the same structural R-action.
Homology and the module/abelian comparison therefore give the asserted scalar identities. -/
theorem pullback_smul {Y : AlgebraicSpace S} (g : Y ⟶ schemeSpace T)
    (h : Y ⟶ X) (w : h ≫ f = g) (N : ModuleCat.{u} R) (n : ℕ) (r : R) :
    (∀ a : H R T e X f (O X) n,
      structurePullback R T e X f g h w n (r • a) =
        r • structurePullback R T e X f g h w n a) ∧
    (∀ a : H R T e X f (coefficients R T e X f N) n,
      coefficientPullback R T e X f g h w N n (r • a) =
        r • coefficientPullback R T e X f g h w N n a) := by
  sorry

/-- Alpha commutes with all T-morphisms, including nonflat maps.
The pure-tensor identity, together with pullback_smul and additivity, is the full
commuting square on the tensor product.
Source: Stacks 06YY, 08IN and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: the coefficient sheaf comparison is normalized on each pure section.
Naturality of the adjunction unit, followed by the same cohomology comparison,
gives this identity. The tensor generators determine the entire square. -/
theorem alpha_geometric {Y : AlgebraicSpace S} (g : Y ⟶ schemeSpace T)
    (h : Y ⟶ X) (w : h ≫ f = g) (N : ModuleCat.{u} R) (n : ℕ)
    (a : H R T e X f (O X) n) (v : N) :
    coefficientPullback R T e X f g h w N n (alpha R T e X f N n (a ⊗ₜ[R] v)) =
      alpha R T e Y g N n ((structurePullback R T e X f g h w n a) ⊗ₜ[R] v) := by
  sorry

/-- Pullback preserves identities on structure and arbitrary coefficient sheaves.
Source: Stacks 06YY and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: the identity adjunction has identity unit and counit. Their normalized
compositors, and the pure-section scalar compositor, cancel in the displayed maps. -/
theorem pullback_id (N : ModuleCat.{u} R) (n : ℕ) :
    (∀ a, structurePullback R T e X f f (𝟙 X) (by simp) n a = a) ∧
    (∀ a, coefficientPullback R T e X f f (𝟙 X) (by simp) N n a = a) := by
  sorry

/-- Pullback preserves compositions, including the canonical coefficient comparisons.
Source: Stacks 06YY and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: composition of the derived adjunction units is the unit of the composite.
Pasting the global-sections comparisons gives the same compatible chart families.
The coefficient compositors agree on 1 tensor v, so the resulting cohomology maps agree. -/
theorem pullback_comp {Y Z : AlgebraicSpace S}
    (g : Y ⟶ schemeSpace T) (q : Z ⟶ schemeSpace T)
    (h : Y ⟶ X) (k : Z ⟶ Y) (w : h ≫ f = g) (v : k ≫ g = q)
    (N : ModuleCat.{u} R) (n : ℕ) :
    (∀ a, structurePullback R T e Y g q k v n
      (structurePullback R T e X f g h w n a) =
        structurePullback R T e X f q (k ≫ h) (by rw [Category.assoc, w, v]) n a) ∧
    (∀ a, coefficientPullback R T e Y g q k v N n
      (coefficientPullback R T e X f g h w N n a) =
        coefficientPullback R T e X f q (k ≫ h)
          (by rw [Category.assoc, w, v]) N n a) := by
  sorry

/-- Pullback preserves the multiplicative unit and cup products.
Source: Stacks 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: insert the derived adjunction unit in both factors of cup. Naturality of
the tensor comparison and the two triangle identities identify the result with
the adjoint of the pulled cup. The same calculation for the unit is the unit triangle. -/
theorem pullback_cup {Y : AlgebraicSpace S} (g : Y ⟶ schemeSpace T)
    (h : Y ⟶ X) (w : h ≫ f = g) :
    structurePullback R T e X f g h w 0 (sectionClass R T e X f (O X) (𝟙 _)) =
      sectionClass R T e Y g (O Y) (𝟙 _) ∧
    ∀ (i j : ℕ) (a : H R T e X f (O X) i) (b : H R T e X f (O X) j),
      structurePullback R T e X f g h w (i + j) (multiply R T e X f i j a b) =
        multiply R T e Y g i j (structurePullback R T e X f g h w i a)
          (structurePullback R T e X f g h w j b) := by
  sorry

/-- Cup is associative, unital, R-bilinear and graded commutative in all degrees.
Source: Stacks 0FPL and 0FPM
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: use associativity and unit triangles for the tensor-of-counits cup.
The cocycle pairing is linear in both cycles. Koszul symmetry on degrees i,j
is multiplication by (-1)^(ij); its involution and cup's symmetry give the last law.
The degree casts below express only associativity, commutativity and zero laws in N. -/
theorem cup_laws :
    (∀ (i j k : ℕ) (a : H R T e X f (O X) i) (b : H R T e X f (O X) j)
      (c : H R T e X f (O X) k),
      castH R T e X f (O X) (Nat.add_assoc i j k)
        (multiply R T e X f (i + j) k (multiply R T e X f i j a b) c) =
      multiply R T e X f i (j + k) a (multiply R T e X f j k b c)) ∧
    (∀ (i : ℕ) (a : H R T e X f (O X) i),
      castH R T e X f (O X) (Nat.zero_add i)
        (multiply R T e X f 0 i (sectionClass R T e X f (O X) (𝟙 _)) a) = a ∧
      castH R T e X f (O X) (Nat.add_zero i)
        (multiply R T e X f i 0 a (sectionClass R T e X f (O X) (𝟙 _))) = a) ∧
    (∀ (i j : ℕ),
      ∃ m : H R T e X f (O X) i →ₗ[R]
        H R T e X f (O X) j →ₗ[R] H R T e X f (O X) (i + j),
        ∀ a b, m a b = multiply R T e X f i j a b) ∧
    (∀ (i j : ℕ) (a : H R T e X f (O X) i) (b : H R T e X f (O X) j),
      castH R T e X f (O X) (Nat.add_comm j i) (multiply R T e X f j i b a) =
        ((-1 : R) ^ (i * j)) • multiply R T e X f i j a b) := by
  sorry

end Laws

section BaseChange
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  (T T' : Over S) (e : T.left ≅ Spec (.of R)) (e' : T'.left ≅ Spec (.of B))
  (g : T' ⟶ T) {X Y : AlgebraicSpace S}
  (f : X ⟶ schemeSpace T) (h : Y ⟶ X) (f' : Y ⟶ schemeSpace T')
  (sq : h ≫ f = f' ≫ groupSchemeMap g)

/-- Scalar extension on an arbitrary coefficient module after change of affine base.
Source: Stacks 03EL (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
abbrev baseModule (N : ModuleCat.{u} R) : ModuleCat.{u} B := ModuleCat.of B (B ⊗[R] N)

include sq in
/-- The base-change coefficient comparison is uniquely fixed on every pure section.
Source: Stacks 03EL and 08IR
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: on charts the map b tensor (a tensor v) goes to b*h-sharp(a) tensor (1 tensor v).
The inverse sends b tensor (c tensor v) to b*h-sharp(c) tensor v. Tensor balancing,
the specified structural ring map, and sheafification give inverse natural maps.
Pure sections generate locally as O-modules, giving uniqueness without flatness of N. -/
theorem baseCoefficient_existsUnique
    (scalars : spaceAffineRingMap e e' g = algebraMap R B) (N : ModuleCat.{u} R) :
    ∃! d : (smallModuleTensorPullback h).obj (coefficients R T e X f N) ≅
        coefficients B T' e' Y f' (baseModule R B N),
      ∀ v : N,
        (Poincare.pullbackUnit h).inv ≫
          (smallModuleTensorPullback h).map ((affineScalarAdjunction R T e X f).unit.app N v) ≫
          d.hom =
        (affineScalarAdjunction B T' e' Y f').unit.app (baseModule R B N) (1 ⊗ₜ[R] v) := by
  sorry

/-- The coefficient comparison retains its complete pure-section normalization.
Source: Stacks 03EL (blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def baseCoefficient (scalars : spaceAffineRingMap e e' g = algebraMap R B)
    (N : ModuleCat.{u} R) :=
  (baseCoefficient_existsUnique R B T T' e e' g f h f' sq scalars N).choose

/-- Canonical base-change pullback on coefficient cohomology, before extending scalars.
Source: Stacks 08IR and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth). -/
def basePullback (scalars : spaceAffineRingMap e e' g = algebraMap R B)
    (N : ModuleCat.{u} R) (n : ℕ) :
    H R T e X f (coefficients R T e X f N) n →+
      H B T' e' Y f' (coefficients B T' e' Y f' (baseModule R B N)) n :=
  pullbackH R T e X f e' g h f' sq _ _
    (baseCoefficient R B T T' e e' g f h f' sq scalars N).hom n

/-- Localization commutes with coefficient comparison, on every pure tensor.
Source: Stacks 08IN, 08IR and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: the structural and coefficient base-change comparisons identify the pulled section
1 tensor v with 1 tensor (1 tensor v). Naturality of the derived adjunction unit and
projection formula gives the identity. Scalar linearity and tensor generation give the
full commuting alpha square. The same identity after the two projection pullbacks gives
the kappa square, since kappa is external cup followed by alpha. -/
theorem localization_alpha (s : R) [IsLocalization.Away s B]
    (scalars : spaceAffineRingMap e e' g = algebraMap R B)
    (N : ModuleCat.{u} R) (n : ℕ) (a : H R T e X f (O X) n) (v : N) :
    basePullback R B T T' e e' g f h f' sq scalars N n
      (alpha R T e X f N n (a ⊗ₜ[R] v)) =
    alpha B T' e' Y f' (baseModule R B N) n
      ((pullbackH R T e X f e' g h f' sq (O X) (O Y)
        (Poincare.pullbackUnit h).hom n a) ⊗ₜ[B] (1 ⊗ₜ[R] v)) := by
  sorry

/-- Flat localization base change on ordinary coefficients is an isomorphism.
The source is B tensor_R H, and its pure-tensor formula fixes the canonical arrow.
Source: Stacks 08IR
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: flat qcqs base change identifies localized derived global sections with
global sections on the Cartesian base change. Exact scalar restriction and flat tensor
commute with homology, including for arbitrary N. The base-change mate is normalized
by the adjunction unit, giving precisely b tensor a maps to b times pulled a.
The tensor universal property gives uniqueness; the derived comparison gives bijectivity. -/
theorem localization_cohomology (s : R) [IsLocalization.Away s B]
    (scalars : spaceAffineRingMap e e' g = algebraMap R B)
    (cartesian : IsPullback h f' f (groupSchemeMap g))
    (hf : MapIsFlat f) (hqc : MapIsQuasiCompact f.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (N : ModuleCat.{u} R) (n : ℕ) :
    ∃! β : (B ⊗[R] H R T e X f (coefficients R T e X f N) n) →ₗ[B]
        H B T' e' Y f' (coefficients B T' e' Y f' (baseModule R B N)) n,
      (∀ (b : B) (a : H R T e X f (coefficients R T e X f N) n),
        β (b ⊗ₜ[R] a) = b • basePullback R B T T' e e' g f h f' sq scalars N n a) ∧
      Function.Bijective β := by
  sorry

/-- Base change preserves cup and its unit, with the actual structural pullback maps.
Source: Stacks 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: naturality of the tensor counits and the geometric derived adjunction unit
identifies both adjoints. The structural unit normalization gives the unit formula.
No flatness of the coefficient ring map or of the geometric map is needed. -/
theorem base_cup :
    pullbackH R T e X f e' g h f' sq (O X) (O Y)
        (Poincare.pullbackUnit h).hom 0 (sectionClass R T e X f (O X) (𝟙 _)) =
      sectionClass B T' e' Y f' (O Y) (𝟙 _) ∧
    ∀ (i j : ℕ) (a : H R T e X f (O X) i) (b : H R T e X f (O X) j),
      pullbackH R T e X f e' g h f' sq (O X) (O Y)
          (Poincare.pullbackUnit h).hom (i + j) (multiply R T e X f i j a b) =
        multiply B T' e' Y f' i j
          (pullbackH R T e X f e' g h f' sq (O X) (O Y)
            (Poincare.pullbackUnit h).hom i a)
          (pullbackH R T e X f e' g h f' sq (O X) (O Y)
            (Poincare.pullbackUnit h).hom j b) := by
  sorry

end BaseChange

section LocalizedProduct
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  (T T' : Over S) (e : T.left ≅ Spec (.of R)) (e' : T'.left ≅ Spec (.of B))
  (t : T' ⟶ T) {X Y X' Y' : AlgebraicSpace S}
  (f : X ⟶ schemeSpace T) (g : Y ⟶ schemeSpace T)
  (f' : X' ⟶ schemeSpace T') (g' : Y' ⟶ schemeSpace T')
  (aX : X' ⟶ X) (aY : Y' ⟶ Y)
  (sqX : aX ≫ f = f' ≫ groupSchemeMap t)
  (sqY : aY ≫ g = g' ≫ groupSchemeMap t)
  (aP : Poincare.product f' g' ⟶ Poincare.product f g)
  (sqP : aP ≫ productMap T f g = productMap T' f' g' ≫ groupSchemeMap t)
  (fstP : aP ≫ Poincare.fst f g = Poincare.fst f' g' ≫ aX)
  (sndP : aP ≫ Poincare.snd f g = Poincare.snd f' g' ≫ aY)

include fstP sndP in
/-- The localization Kunneth square on all homogeneous pure tensors.
These generate the localized tensor of direct sums; hence this is the entire square.
Source: Stacks 08IR and 0H9A
(blueprint: lem-sfb-projective-cohomology-coefficient-kunneth).
Proof: expand kappa by its generator formula. The two commuting projection squares
identify the pulled external class using composition of geometric adjunction units.
Base change preserves cup. The pure-section coefficient comparison identifies v with
1 tensor v; localization_alpha then identifies the final coefficient map. Linearity,
direct-sum generation and tensor generation give the full square. -/
theorem localization_kappa (s : R) [IsLocalization.Away s B]
    (scalars : spaceAffineRingMap e e' t = algebraMap R B)
    (N : ModuleCat.{u} R) (i j : ℕ)
    (a : H R T e X f (O X) i) (b : H R T e Y g (O Y) j) (v : N) :
    basePullback R B T T' e e' t (productMap T f g) aP (productMap T' f' g') sqP
        scalars N (i + j)
        (kappa R T e f g N (i + j) (includeTensor R T e f g i j a b ⊗ₜ[R] v)) =
      kappa B T' e' f' g' (baseModule R B N) (i + j)
        (includeTensor B T' e' f' g' i j
          (pullbackH R T e X f e' t aX f' sqX (O X) (O X')
            (Poincare.pullbackUnit aX).hom i a)
          (pullbackH R T e Y g e' t aY g' sqY (O Y) (O Y')
            (Poincare.pullbackUnit aY).hom j b) ⊗ₜ[B] (1 ⊗ₜ[R] v)) := by
  sorry

end LocalizedProduct


end AlgebraicGeometry.AlgebraicSpace.ProjectiveKunneth
