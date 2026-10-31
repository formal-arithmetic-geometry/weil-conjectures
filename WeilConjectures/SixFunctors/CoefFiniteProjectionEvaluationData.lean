/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSystemProjectionEvaluation
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains

/-! # Finite normalization of the system projection-evaluation word

Source: blueprint latest, prop-coef-integral-dualizing.proof.md, paragraph 2;
Stacks 07A6 and 0B56 (blueprint: def-coef-finite-projection-evaluation-data).

All point sections take values in ordinary derived categories of towers, before limits.
Index n denotes the positive coefficient exponent n + 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Modules at the quotient point, with the same lift as the sequence site.
Source: Stacks 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
abbrev FinitePointModules (n : ℕ) := ModuleCat.{u + 1} (compactSupportSystemLevel l E n)

/-- The standard ordinary unbounded localization at the finite point.
Source: Stacks 05RU (blueprint: def-coef-finite-projection-evaluation-data). -/
instance finitePointHasDerived (n : ℕ) :
    HasDerivedCategory.{u + 2} (FinitePointModules l E n) :=
  HasDerivedCategory.standard _

/-- Exact evaluation of quotient-linear point towers, without inverse limit.
Source: Stacks 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
def finitePointEvaluation (n : ℕ) :
    DerivedCategory (coefHomQuotientPointModules.{u, u} l E) ⥤
      DerivedCategory (FinitePointModules l E n) :=
  letI := finitePointHasDerived l E n
  letI : (PresheafOfModules.evaluation (coefHomPointQuotientRing.{u, u} l E)
      (op n)).Additive := { map_add := rfl }
  letI := PresheafOfModules.evaluation_preservesFiniteLimits
    (R := coefHomPointQuotientRing.{u, u} l E) (op n)
  letI := PresheafOfModules.Finite.evaluation_preservesFiniteColimits
    (R := coefHomPointQuotientRing.{u, u} l E) (op n)
  Functor.mapDerivedCategory.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (PresheafOfModules.evaluation (coefHomPointQuotientRing.{u, u} l E) (op n))

/-- Actual finite scalar restriction along the quotient R to A_(n+1).
Source: Stacks 07A6 (blueprint: def-coef-finite-projection-evaluation-data). -/
abbrev finiteScalarRestriction (n : ℕ) :
    FinitePointModules l E n ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
  ModuleCat.restrictScalars.{u + 1} (coefHomPointScalarComponent.{u, u} l E n).hom

/-- Exact localization of finite scalar restriction.
Source: Stacks 07A6 (blueprint: def-coef-finite-projection-evaluation-data). -/
def finiteDerivedRestriction (n : ℕ) :
    DerivedCategory (FinitePointModules l E n) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  (finiteScalarRestriction l E n).mapDerivedCategory

/-- Actual quotient-linear finite sections, using the constant-sheaf unit at W.
Source: Stacks 03DA, 08JA (blueprint: def-coef-finite-projection-evaluation-data). -/
def finiteSections (W : Scheme.{u}) (n : ℕ) :
    normalizedDVRModules.{u, u} l E W n ⥤ FinitePointModules l E n :=
  SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 W))) ⋙
    ModuleCat.restrictScalars (coefHomQuotientSectionScalarComponent.{u, u} l E W n).hom

/-- Additivity of ordinary finite sections follows from the two actual functors.
Source: Stacks 03DA (blueprint: def-coef-finite-projection-evaluation-data). -/
instance finiteSectionsAdditive (W : Scheme.{u}) (n : ℕ) :
    (finiteSections l E W n).Additive where
  map_add := rfl

/-- Finite derived sections with quotient action, on arbitrary unbounded inputs.
Source: Stacks 08JA (blueprint: def-coef-finite-projection-evaluation-data). -/
def finiteDerivedSections (W : Scheme.{u}) (n : ℕ) :=
  letI : IsGrothendieckAbelian.{u + 1} (normalizedDVRModules.{u, u} l E W n) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{
    u + 1, u, u} (ProEt.topology W) (integralCoefficientCommRingSheaf.{u, u} l E W n)).1
  (finiteSections l E W n).rightDerivedFunctor


/-- The recorded K-injective resolutions at each actual finite coefficient site.
Source: Stacks 079P (blueprint: def-coef-finite-projection-evaluation-data). -/
instance finiteSiteGrothendieck (W : Scheme.{u}) (n : ℕ) :
    IsGrothendieckAbelian.{u + 1} (normalizedDVRModules.{u, u} l E W n) :=
  (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    (ProEt.topology W) (integralCoefficientCommRingSheaf.{u, u} l E W n)).1

/-- The native exact finite geometric inverse image.
Source: Stacks 07A4 (blueprint: def-coef-finite-projection-evaluation-data). -/
abbrev finitePull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) f).mapDerivedCategory

/-- Native finite proper image, derived separately after open extension.
Source: Stacks 07A5 (blueprint: def-coef-finite-projection-evaluation-data). -/
def finitePush {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  letI : IsGrothendieckAbelian.{u + 1} (normalizedDVRModules.{u, u} l E X n) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
      (ProEt.topology X) (integralCoefficientCommRingSheaf.{u, u} l E X n)).1
  (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f).rightDerivedFunctor

/-- The native finite geometric adjunction with the ordinary module normalization.
Source: Stacks 07A6 (blueprint: def-coef-finite-projection-evaluation-data). -/
def finiteAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finitePull l E f n ⊣ finitePush l E f n :=
  letI : IsGrothendieckAbelian.{u + 1} (normalizedDVRModules.{u, u} l E X n) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
      (ProEt.topology X) (integralCoefficientCommRingSheaf.{u, u} l E X n)).1
  (proEtaleRingModuleAdjunction f
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Y)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) f))
      |>.mapDerivedCategoryRightDerivedAdjunction

/-- The finite compact-support functor in native quotient coefficients.
Source: Stacks 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
def finiteSupport {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) (n : ℕ) :=
  (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) c.i).mapDerivedCategory ⋙
    finitePush l E c.g n

/-- Fixed coefficient-size abelian sheafification on the finite site.
Source: Stacks 03DA (blueprint: def-coef-finite-projection-evaluation-data). -/
instance (priority := 30000) finiteAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W

/-- The fixed coefficient-size local-bijectivity criterion.
Source: Stacks 03DA (blueprint: def-coef-finite-projection-evaluation-data). -/
instance (priority := 30000) finiteAbLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual finite-site monoidal structure, with its coefficient sizes fixed.
Source: Stacks 03EK (blueprint: def-coef-finite-projection-evaluation-data). -/
@[instance_reducible]
def finiteSiteMonoidal (W : Scheme.{u}) (n : ℕ) :
    MonoidalCategory (normalizedDVRModules.{u, u} l E W n) :=
  @cochainModulesMonoidal.{u + 1, u, u + 1} W.ProEt _
    (ProEtale.VaryingRing.siteSmall W) (ProEt.topology W) _
    (integralCoefficientCommRingSheaf.{u, u} l E W n)

attribute [instance 3000] finiteSiteMonoidal

/-- Additivity of the native finite direct image.
Source: Stacks 03DA (blueprint: def-coef-finite-projection-evaluation-data). -/
instance (priority := 3000) finitePushAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f).Additive :=
  ProEtale.StrictTower.moduleDirectImage_additive _ f

/-- Bilinearity of the actual finite sheaf tensor.
Source: Stacks 03EK (blueprint: def-coef-finite-projection-evaluation-data). -/
instance (priority := 3000) finiteSitePreadditive (W : Scheme.{u}) (n : ℕ) :
    @MonoidalPreadditive (normalizedDVRModules.{u, u} l E W n) _ _
      (finiteSiteMonoidal l E W n) :=
  @cochainModulesPreadditive.{u + 1, u, u + 1} W.ProEt _
    (ProEtale.VaryingRing.siteSmall W) (ProEt.topology W) _
    (integralCoefficientCommRingSheaf.{u, u} l E W n)

/-- Normalized finite composition of point sections with direct image along a.
The ordinary comparison is restriction along the inverse terminal-object base-change
isomorphism; the derived comparison is fixed by the universal right-derived units.
Source: Stacks 0D6D, 0D6E (blueprint: def-coef-finite-projection-evaluation-data). -/
structure FiniteSectionsComposition {X Y : Scheme.{u}} (a : X ⟶ Y) (n : ℕ) where
  ordinary : ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) a ⋙
    finiteSections l E Y n ≅ finiteSections l E X n
  sections : ∀ (M : normalizedDVRModules.{u, u} l E X n)
    (x : (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) a ⋙
      finiteSections l E Y n).obj M),
    HEq ((ordinary.hom.app M) x) ((M.val.map (terminalPullback a).inv.op) x)
  derived : finitePush l E a n ⋙ finiteDerivedSections l E Y n ≅ finiteDerivedSections l E X n
  normalization : @DerivedCompositionNormalization
    (normalizedDVRModules.{u, u} l E X n) _ _ _
    (normalizedDVRModules.{u, u} l E Y n) _ _ _
    (FinitePointModules l E n) _ _ _
    (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) a)
    (finitePushAdditive l E a n)
    (finiteSections l E Y n) (finiteSectionsAdditive l E Y n)
    (finiteSections l E X n) (finiteSectionsAdditive l E X n)
    (finitePush l E a n) (finiteDerivedSections l E Y n) (finiteDerivedSections l E X n)
    (rightUnit (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) a))
    (rightUnit (finiteSections l E Y n)) (rightUnit (finiteSections l E X n))
    ordinary derived

/-- The ordinary finite sections tensor, fixed on actual local pure tensors.
Source: Stacks 03EK, 0B56 (blueprint: def-coef-finite-projection-evaluation-data). -/
structure FiniteSectionsTensor (W : Scheme.{u}) (n : ℕ) where
  map : ∀ M N : normalizedDVRModules.{u, u} l E W n,
    (finiteSections l E W n).obj M ⊗ (finiteSections l E W n).obj N ⟶
      (finiteSections l E W n).obj (M ⊗ N)
  pure : ∀ (M N : normalizedDVRModules.{u, u} l E W n)
    (x : ((finiteSections l E W n).obj M)) (y : ((finiteSections l E W n).obj N)),
    HEq ((map M N) (x ⊗ₜ y))
      (@SemilinearSections.tensorSection.{u + 1, u, u + 1} W.ProEt _
        (ProEt.topology W) (ProEtale.VaryingRing.siteSmall W)
        (integralCoefficientCommRingSheaf.{u, u} l E W n) M N (op (ProEt.mk (𝟙 W))) x y)

/-- The ordinary finite proper-image tensor, with its actual base-changed sections.
Source: Stacks 03EK, 0B56 (blueprint: def-coef-finite-projection-evaluation-data). -/
structure FinitePushTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) where
  map : ∀ M N : normalizedDVRModules.{u, u} l E X n,
    (finiteSiteMonoidal l E Y n).tensorObj
      ((ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f).obj M)
      ((ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f).obj N) ⟶
    (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f).obj
      ((finiteSiteMonoidal l E X n).tensorObj M N)
  pure : ∀ (M N : normalizedDVRModules.{u, u} l E X n) (V : Y.ProEtᵒᵖ)
    (x : ((ProEtale.StrictTower.moduleDirectImage
      (compactSupportSystemLevel l E n) f).obj M).val.obj V)
    (y : ((ProEtale.StrictTower.moduleDirectImage
      (compactSupportSystemLevel l E n) f).obj N).val.obj V),
    HEq (((map M N).val.app V)
      (@SemilinearSections.tensorSection.{u + 1, u, u + 1} Y.ProEt _
        (ProEt.topology Y) (ProEtale.VaryingRing.siteSmall Y)
        (integralCoefficientCommRingSheaf.{u, u} l E Y n) _ _ V x y))
      (@SemilinearSections.tensorSection.{u + 1, u, u + 1} X.ProEt _
        (ProEt.topology X) (ProEtale.VaryingRing.siteSmall X)
        (integralCoefficientCommRingSheaf.{u, u} l E X n) M N ((proEtaleBaseChange f).op.obj V) x y)

/-- Finite scalar balancing on ordinary modules, fixed by x tensor y to x tensor y.
Source: Stacks 07A6, 0B56 (blueprint: def-coef-finite-projection-evaluation-data). -/
structure FiniteRestrictionTensor (n : ℕ) where
  map : ∀ H B : FinitePointModules l E n,
    (finiteScalarRestriction l E n).obj H ⊗ (finiteScalarRestriction l E n).obj B ⟶
      (finiteScalarRestriction l E n).obj (H ⊗ B)
  pure : ∀ (H B : FinitePointModules l E n) (x : H) (y : B),
    HEq ((map H B) (x ⊗ₜ y)) (x ⊗ₜ[compactSupportSystemLevel l E n] y)

/-- Universal tensor localization at one finite site, retaining the K-flat comparison
and signed symmetry of the existing closed tensor-Hom structure.
Source: Stacks 06YT, 08J9 (blueprint: def-coef-finite-projection-evaluation-data). -/
structure FiniteSiteTensor (W : Scheme.{u})
    (S : CoefficientDerivedSystemTensors.{u, u} l E W) (n : ℕ) where
  localization : TensorLocalization (S.finiteClosed n).tensor
  totalComparison : coefficientTotalTensor.{u + 1, u + 1, u}
    (ProEt.topology W) (integralCoefficientCommRingSheaf.{u, u} l E W n) ≅
      (total : CochainComplex (normalizedDVRModules.{u, u} l E W n) ℤ ×
        CochainComplex (normalizedDVRModules.{u, u} l E W n) ℤ ⥤ _)
  total_pure : ∀ (P Q : CochainComplex (normalizedDVRModules.{u, u} l E W n) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    HEq ((((totalComparison.hom.app (P, Q)).f k).val.app V)
      (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology W)
        (integralCoefficientCommRingSheaf.{u, u} l E W n) P Q p q k h V x y))
      (((HomologicalComplex.ιTensorObj P Q p q k h).val.app V)
        (@SemilinearSections.tensorSection.{u + 1, u, u + 1} W.ProEt _
          (ProEt.topology W) (ProEtale.VaryingRing.siteSmall W)
          (integralCoefficientCommRingSheaf.{u, u} l E W n) (P.X p) (Q.X q) V x y))
  compatibility : ∀ P Q hP hQ,
    ((S.finiteTensorModel n).iso _ _ _ P Q hP hQ).hom ≫
        localization.comparison.app (P, Q) =
      DerivedCategory.Q.map (totalComparison.hom.app (P, Q))
  symmetry : @SymmetricCategory (normalizedDVRDerived.{u, u} l E W n) _
    (S.finiteClosed n).monoidal
  signed : RingedDerivedTensorSymmetryModel (ProEt.topology W)
    (integralCoefficientCommRingSheaf.{u, u} l E W n) (S.finiteClosed n)
    (S.finiteTensorModel n) symmetry

/-- Finite canonical operations and tensor mates. Every ordinary lax tensor is fixed on
pure tensors; every derived strong tensor is fixed by TensorAdjunction.representative.
The point symmetry is the localization of the signed swap on total complexes, and the
sections pullback composition is conjugate to the normalized finite sections composition.
These are witnesses in the conclusion, never extra assumptions on the scheme or inputs.
Source: Stacks 07A4, 07A6, 0B56 (blueprint: def-coef-finite-projection-evaluation-data). -/
structure FiniteModel {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
    (m : Model l E c) (n : ℕ) where
  [quotient : MonoidalCategory (DerivedCategory (FinitePointModules l E n))]
  quotientLocalization : TensorLocalization (MonoidalCategory.tensor
    (DerivedCategory (FinitePointModules l E n)))
  [integral : MonoidalCategory (DerivedCategory (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))]
  integralLocalization : TensorLocalization (MonoidalCategory.tensor
    (DerivedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))))
  symmetry : SymmetricCategory (DerivedCategory (FinitePointModules l E n))
  chain : ∀ P Q : CochainComplex (FinitePointModules l E n) ℤ,
    total.obj (P, Q) ≅ total.obj (Q, P)
  signed : ∀ (P Q : CochainComplex (FinitePointModules l E n) ℤ) (p q d : ℤ)
    (h : p + q = d) (h' : q + p = d) (e₁ : P.X p) (e₂ : Q.X q),
    ((chain P Q).hom.f d) (HomologicalComplex.ιTensorObj P Q p q d h (e₁ ⊗ₜ e₂)) =
      (p * q).negOnePow • HomologicalComplex.ιTensorObj Q P q p d h' (e₂ ⊗ₜ e₁)
  localization : ∀ P Q : CochainComplex (FinitePointModules l E n) ℤ,
    (symmetry.toBraidedCategory.braiding (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj Q)).hom ≫ quotientLocalization.comparison.app (Q, P) =
      quotientLocalization.comparison.app (P, Q) ≫ DerivedCategory.Q.map (chain P Q).hom
  x : FiniteSiteTensor l E X m.x.data n
  y : FiniteSiteTensor l E Y m.y.data n
  z : FiniteSiteTensor l E c.Z m.z.data n
  xLax : FiniteSectionsTensor l E X n
  yLax : FiniteSectionsTensor l E Y n
  pLax : FinitePushTensor l E c.g n
  rLax : FiniteRestrictionTensor l E n
  gx : AdjointLocalization (finiteSections l E X n) (finiteDerivedSections l E X n)
    (rightUnit (finiteSections l E X n))
  gy : AdjointLocalization (finiteSections l E Y n) (finiteDerivedSections l E Y n)
    (rightUnit (finiteSections l E Y n))
  p : AdjointLocalization
    (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) c.g)
    (finitePush l E c.g n)
    (rightUnit (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) c.g))
  r : AdjointLocalization (finiteScalarRestriction l E n) (finiteDerivedRestriction l E n)
    ((finiteScalarRestriction l E n).mapDerivedCategoryFactors.inv)
  gxTensor : TensorAdjunction (MonoidalCategory.tensor _)
    (m.x.data.finiteClosed n).tensor quotientLocalization x.localization
    (finiteSections l E X n) (finiteDerivedSections l E X n)
    (rightUnit (finiteSections l E X n)) xLax.map gx
  gyTensor : TensorAdjunction (MonoidalCategory.tensor _)
    (m.y.data.finiteClosed n).tensor quotientLocalization y.localization
    (finiteSections l E Y n) (finiteDerivedSections l E Y n)
    (rightUnit (finiteSections l E Y n)) yLax.map gy
  pTensor : @TensorAdjunction
    (normalizedDVRModules.{u, u} l E Y n) _ _ _ _ _ _
    (normalizedDVRModules.{u, u} l E c.Z n) _ _ _ _ _ _
    (m.y.data.finiteClosed n).tensor
    (m.z.data.finiteClosed n).tensor y.localization z.localization
    (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) c.g)
    (finitePushAdditive l E c.g n) (finitePush l E c.g n)
    (rightUnit (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) c.g))
    pLax.map p
  rTensor : TensorAdjunction (MonoidalCategory.tensor _) (MonoidalCategory.tensor _)
    integralLocalization quotientLocalization
    (finiteScalarRestriction l E n) (finiteDerivedRestriction l E n)
    ((finiteScalarRestriction l E n).mapDerivedCategoryFactors.inv) rLax.map r
  sectionsComposition : FiniteSectionsComposition l E a n
  openTensor : CoefSupportOpenTensor.FiniteOpenModel l E c.i m.x.data m.z.data n

namespace FiniteModel
variable {l E} {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
  {m : Model l E c} {n : ℕ} (f : FiniteModel l E m n)

/-- The quotient tensor at the finite point.
Source: Stacks 07A4 (blueprint: def-coef-finite-projection-evaluation-data). -/
abbrev qTensor := @MonoidalCategory.tensor _ _ f.quotient

/-- The integral tensor at the finite point.
Source: Stacks 07A4 (blueprint: def-coef-finite-projection-evaluation-data). -/
abbrev integralTensor := @MonoidalCategory.tensor _ _ f.integral

/-- Finite quotient-linear global Hom, retaining its actual quotient action.
Source: Stacks 08JA (blueprint: def-coef-finite-projection-evaluation-data). -/
abbrev h (_f : FiniteModel l E m n) (U N : normalizedDVRDerived.{u, u} l E X n) :=
  (finiteDerivedSections l E X n).obj ((coefficientFiniteInternalHom l E X n).obj (op U, N))

/-- Finite compact-support sections, before any scalar restriction.
Source: Stacks 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
abbrev b (_f : FiniteModel l E m n) (U : normalizedDVRDerived.{u, u} l E X n) :=
  (finiteDerivedSections l E Y n).obj ((finiteSupport l E c n).obj U)

/-- Canonical finite pullback composition, obtained by conjugating the normalized
finite sections composition through the actual derived adjunctions.
Source: Stacks 0D6D (blueprint: def-coef-finite-projection-evaluation-data). -/
def composition : f.gy.left ⋙ finitePull l E a n ≅ f.gx.left :=
  Adjunction.leftAdjointCompIso f.gy.adjunction (finiteAdjunction l E a n)
    f.gx.adjunction f.sectionsComposition.derived

/-- The finite sections counit after the pullback-composition comparison.
Source: Stacks 07A6, 0D6D (blueprint: def-coef-finite-projection-evaluation-data). -/
def t (U N : normalizedDVRDerived.{u, u} l E X n) :
    (finitePull l E a n).obj (f.gy.left.obj (f.h U N)) ⟶
      (coefficientFiniteInternalHom l E X n).obj (op U, N) :=
  f.composition.hom.app (f.h U N) ≫ f.gx.adjunction.counit.app _

/-- Signed finite closed evaluation after the ordinary finite sections counit.
Source: Stacks 08J9, 0FPT (blueprint: def-coef-finite-projection-evaluation-data). -/
def v (U N : normalizedDVRDerived.{u, u} l E X n) :
    (m.x.data.finiteClosed n).tensor.obj
      (U, (finitePull l E a n).obj (f.gy.left.obj (f.h U N))) ⟶ N :=
  (m.x.data.finiteClosed n).tensor.map (Prod.mkHom (𝟙 U) (f.t U N)) ≫
    (f.x.symmetry.toBraidedCategory.braiding U
      ((coefficientFiniteInternalHom l E X n).obj (op U, N))).hom ≫
    (m.x.data.finiteClosed n).evaluation U N

/-- The proper tensor comparison transported through the uniquely compatible adjoints.
Source: Stacks 07A4, 07A6 (blueprint: def-coef-finite-projection-evaluation-data). -/
def properTensor : (m.y.data.finiteClosed n).tensor ⋙ finitePull l E c.g n ≅
    ((finitePull l E c.g n).prod (finitePull l E c.g n)) ⋙
      (m.z.data.finiteClosed n).tensor :=
  letI := finitePushAdditive l E c.g n
  transportTensor _ _ (f.p.adjunction.leftAdjointUniq (finiteAdjunction l E c.g n))
    f.pTensor.comparison

/-- The native finite pullback compositor with the fixed compactification equation.
Source: Stacks 0D6D (blueprint: def-coef-finite-projection-evaluation-data). -/
def compactificationPullback (_f : FiniteModel l E m n) :
    finitePull l E c.g n ⋙ finitePull l E c.i n ≅
    finitePull l E a n :=
  (Functor.mapDerivedCategoryCompIso
    (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) c.g)
    (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) c.i)).symm ≪≫
  Functor.mapDerivedCategoryNatIso
    (ProEtale.StrictTower.moduleGComp (compactSupportSystemLevel l E n) c.i c.g).symm ≪≫
  eqToIso (congrArg (fun b ↦ finitePull l E b n) c.comm.symm)

/-- The ambient compact-support projection: the proper counit mate, the actual finite
open chain comparison, and the native pullback compositor, in that order.
This is the uncurried word of def-exchange-projection, with its open factor specified.
Source: Stacks 0B56, 0E8I, 0D6D (blueprint: def-coef-finite-projection-evaluation-data). -/
def Pi (U : normalizedDVRDerived.{u, u} l E X n)
    (L : normalizedDVRDerived.{u, u} l E Y n) :
    (m.y.data.finiteClosed n).tensor.obj ((finiteSupport l E c n).obj U, L) ⟶
      (finiteSupport l E c n).obj ((m.x.data.finiteClosed n).tensor.obj
        (U, (finitePull l E a n).obj L)) :=
  derivedProjectionFormulaMate (finitePull l E c.g n) (finitePush l E c.g n)
    (finiteAdjunction l E c.g n) (m.y.data.finiteClosed n).tensor
    (m.z.data.finiteClosed n).tensor f.properTensor
    ((ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) c.i).mapDerivedCategory.obj
      U) L ≫
    (finitePush l E c.g n).map
      ((CoefSupportOpenTensor.finiteGamma l E c.i m.x.data m.z.data n f.openTensor).hom.app
        (U, (finitePull l E c.g n).obj L) ≫
        (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) c.i).mapDerivedCategory.map
          ((m.x.data.finiteClosed n).tensor.map
            (Prod.mkHom (𝟙 U) (f.compactificationPullback.hom.app L))))

/-- Finite sections projection, ambient support projection, and finite closed evaluation.
Source: Stacks 0B56, 08J9 (blueprint: def-coef-finite-projection-evaluation-data). -/
def q (U N : normalizedDVRDerived.{u, u} l E X n) :
    f.qTensor.obj (f.b U, f.h U N) ⟶ f.b N :=
  projection f.gyTensor ((finiteSupport l E c n).obj U) (f.h U N) ≫
    (finiteDerivedSections l E Y n).map
      (f.Pi U (f.gy.left.obj (f.h U N)) ≫ (finiteSupport l E c n).map (f.v U N))

/-- Scalar balancing is the scalar projection mate followed by its restriction counit.
Its ordinary lax tensor is fixed on pure tensors by FiniteRestrictionTensor.pure.
Source: Stacks 07A6, 0B56 (blueprint: def-coef-finite-projection-evaluation-data). -/
def balance (H B : DerivedCategory (FinitePointModules l E n)) :
    f.integralTensor.obj ((finiteDerivedRestriction l E n).obj H,
      (finiteDerivedRestriction l E n).obj B) ⟶
      (finiteDerivedRestriction l E n).obj (f.qTensor.obj (H, B)) :=
  projection f.rTensor H ((finiteDerivedRestriction l E n).obj B) ≫
    (finiteDerivedRestriction l E n).map
      (f.qTensor.map (Prod.mkHom (𝟙 H) (f.r.adjunction.counit.app B)))

/-- The displayed finite pairing: scalar balancing, signed symmetry, the finite sections
mate, ambient support projection and finite evaluation after the sections counit.
Source: blueprint paragraph 2; Stacks 07A6, 0B56
(blueprint: def-coef-finite-projection-evaluation-data). -/
def beta (U N : normalizedDVRDerived.{u, u} l E X n) :
    f.integralTensor.obj ((finiteDerivedRestriction l E n).obj (f.h U N),
      (finiteDerivedRestriction l E n).obj (f.b U)) ⟶
      (finiteDerivedRestriction l E n).obj (f.b N) :=
  f.balance (f.h U N) (f.b U) ≫ (finiteDerivedRestriction l E n).map
    ((f.symmetry.toBraidedCategory.braiding (f.h U N) (f.b U)).hom ≫ f.q U N)

end FiniteModel

/-- Ordinary point evaluation, with its additive and exact instances recorded by the
finite-evaluation construction above.
Source: Stacks 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
abbrev quotientEvaluation (n : ℕ) : coefHomQuotientPointModules.{u, u} l E ⥤
    FinitePointModules l E n :=
  PresheafOfModules.evaluation.{u + 1} (coefHomPointQuotientRing.{u, u} l E) (op n)

/-- Additivity of evaluation keeps the component of each sum unchanged.
Source: Stacks 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
instance quotientEvaluationAdditive (n : ℕ) : (quotientEvaluation l E n).Additive where
  map_add := rfl

/-- Left exactness is the existing presheaf-module evaluation instance.
Source: Stacks 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
instance quotientEvaluationLimits (n : ℕ) : PreservesFiniteLimits (quotientEvaluation l E n) :=
  PresheafOfModules.evaluation_preservesFiniteLimits _ _

/-- Right exactness is the existing presheaf-module evaluation instance.
Source: Stacks 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
instance quotientEvaluationColimits (n : ℕ) : PreservesFiniteColimits (quotientEvaluation l E n) :=
  PresheafOfModules.Finite.evaluation_preservesFiniteColimits _ _

/-- The point restriction/evaluation square, with no scalar or section changed.
Source: Stacks 07A6, 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
def restrictionEvaluation (n : ℕ) :
    coefHomPointDerivedRestriction.{u, u} l E ⋙ coefHomPointEvaluation l E n ≅
      finitePointEvaluation l E n ⋙ finiteDerivedRestriction l E n :=
  letI := finitePointHasDerived l E n
  letI := coefHomFinitePointHasDerived.{u, u} l E
  (Functor.mapDerivedCategoryCompIso (coefHomPointRestriction l E)
    ((evaluation ℕᵒᵖ _).obj (op n))).symm ≪≫
  Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1,
    u + 2, u + 2, u + 2} (D := FinitePointModules l E n)
    (quotientEvaluation l E n) (finiteScalarRestriction l E n)

/-- A derived tensor evaluation is fixed by the ordinary strong tensor comparison
on all complexes and the universal tensor localization comparisons. Its ordinary
component is separately normalized on actual pure tensors in FiniteEvaluation.
Source: Stacks 06YT, 07A4 (blueprint: def-coef-finite-projection-evaluation-data). -/
structure TensorEvaluation
    {A B : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
    [Abelian A] [Abelian B] [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    [HasDerivedCategory.{u + 2} A] [HasDerivedCategory.{u + 2} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (TA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (TB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (tA : TensorLocalization TA) (tB : TensorLocalization TB) where
  ordinary : ∀ M N : A, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N
  naturality : ∀ {M M' N N' : A} (a : M ⟶ M') (b : N ⟶ N'),
    F.map (a ⊗ₘ b) ≫ (ordinary M' N').hom =
      (ordinary M N).hom ≫ (F.map a ⊗ₘ F.map b)
  derived : TA ⋙ F.mapDerivedCategory ≅ (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ TB
  normalization : ∀ P Q : CochainComplex A ℤ,
    derived.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        F.mapDerivedCategory.map (tA.comparison.app (P, Q)) ≫
        F.mapDerivedCategoryFactors.hom.app (total.obj (P, Q)) =
      TB.map (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
          (F.mapDerivedCategoryFactors.hom.app Q)) ≫
        tB.comparison.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P, (F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map (tensorPullbackTotal F ordinary naturality P Q)

/-- Localization comparison for point evaluation in the fixed ordinary localization.
Source: Stacks 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
def quotientEvaluationFactors (n : ℕ) : DerivedCategory.Q ⋙ finitePointEvaluation l E n ≅
    (quotientEvaluation l E n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.mapDerivedCategoryFactors.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C₂ := FinitePointModules l E n) (quotientEvaluation l E n)

/-- Additivity of the evaluated finite sections composite.
Source: Stacks 03DA (blueprint: def-coef-finite-projection-evaluation-data). -/
instance finiteEvaluatedSectionsAdditive (W : Scheme.{u}) (n : ℕ) :
    (coefficientSequenceEvaluation.{u, u} l E W n ⋙ finiteSections l E W n).Additive :=
  letI := coefficientSequenceEvaluation_additiveInstance.{u, u} l E W n
  letI := finiteSectionsAdditive l E W n
  inferInstance

/-- Canonical finite sections comparison, normalized by the actual ordinary sections
and by the two universal right-derived units, without a K-injective evaluation premise.
Source: Stacks 0D6E, 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
structure SectionsEvaluation (W : Scheme.{u}) (n : ℕ) where
  ordinary : coefHomQuotientSections l E W ⋙ quotientEvaluation l E n ≅
    coefficientSequenceEvaluation l E W n ⋙ finiteSections l E W n
  sections : ∀ (M : coefficientSequenceModules.{u, u} l E W)
    (x : ((coefHomQuotientSections l E W).obj M).obj (op n)),
    HEq ((ordinary.hom.app M) x) x
  derived : coefHomQuotientDerivedSections l E W ⋙ finitePointEvaluation l E n ≅
    coefficientSequenceDerivedEvaluation l E W n ⋙ finiteDerivedSections l E W n
  normalization : ∀ P : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ,
    (finitePointEvaluation l E n).map
        ((rightUnit (coefHomQuotientSections l E W)).app P) ≫
        derived.hom.app (DerivedCategory.Q.obj P) ≫
        (finiteDerivedSections l E W n).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app P) =
      (quotientEvaluationFactors l E n).hom.app
          (((coefHomQuotientSections l E W).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (F := coefHomQuotientSections l E W)
            (G := quotientEvaluation l E n) ordinary (.up ℤ)).hom.app P) ≫
        (rightUnit (finiteSections l E W n)).app
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P)



universe a₁ a₂ b₁ b₂ v₁ v₂ w₁ w₂

/-- Preservation of a specified strong tensor comparison by exact evaluation.
Source: Stacks 07A4 (blueprint: def-coef-finite-projection-evaluation-data). -/
def StrongTensorEvaluation
    {A : Type a₁} {B : Type b₁} {A' : Type a₂} {B' : Type b₂}
    [Category.{v₁} A] [Category.{w₁} B] [Category.{v₂} A'] [Category.{w₂} B']
    {TA : A × A ⥤ A} {TB : B × B ⥤ B}
    {TA' : A' × A' ⥤ A'} {TB' : B' × B' ⥤ B'}
    {L : A ⥤ B} {L' : A' ⥤ B'}
    (μ : TA ⋙ L ≅ L.prod L ⋙ TB) (μ' : TA' ⋙ L' ≅ L'.prod L' ⋙ TB')
    (eA : A ⥤ A') (eB : B ⥤ B')
    (left : L ⋙ eB ≅ eA ⋙ L')
    (tensorA : TA ⋙ eA ≅ eA.prod eA ⋙ TA')
    (tensorB : TB ⋙ eB ≅ eB.prod eB ⋙ TB') : Prop :=
  ∀ U V : A,
    eB.map (μ.hom.app (U, V)) ≫ tensorB.hom.app (L.obj U, L.obj V) ≫
        TB'.map (Prod.mkHom (left.hom.app U) (left.hom.app V)) =
      left.hom.app (TA.obj (U, V)) ≫ L'.map (tensorA.hom.app (U, V)) ≫
        μ'.hom.app (eA.obj U, eA.obj V)

/-- The native support evaluation, separately evaluating proper image and exact open
extension. It applies to arbitrary inputs, without a cartesianness assumption.
Source: Stacks 0941 (blueprint: def-coef-finite-projection-evaluation-data). -/
def supportEvaluation {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) (n : ℕ) :
    CoefSupportOpenTensor.operation l E c ⋙ coefficientSequenceDerivedEvaluation l E Y n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙ finiteSupport l E c n :=
  Functor.isoWhiskerLeft
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i)
    (ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g n) ≪≫
  Functor.isoWhiskerRight
    (ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i n) (finitePush l E c.g n)


end WeilConjectures.CoefProjectionEvaluation
