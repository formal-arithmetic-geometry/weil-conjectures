/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjectionIso
import WeilConjectures.AlgebraicGeometry.SupportedConstructibleOriginComparison.SupportedConstructibleOriginComparison
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormulaBounded

/-! # Bounded etale origin of an open-supported coefficient tensor

Source: blueprint main-20261015, `sk-lem-sp-reduction-direct-image.proof.md`, Step 1;
Stacks Tags 09AK, 09AL, 09AF, 07A4, 08FZ, 0GL1, 099T
(blueprint: lem-sp-supported-etale-tensor-origin).

The small-site fixed-module presentation uses ULift of the finite coefficient ring.
The Tor hypothesis and the scalar-extension target use the recorded intrinsic realization.
All displayed identifications below are actual composites of canonical comparisons,
including the section-normalized realization square and adjunction mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ d₁ d₂ d₃ d₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
namespace SupportedEtaleTensorOrigin

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

private theorem mate_of_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ C} {H : C ⥤ A} {G : B ⥤ D} {K : D ⥤ B}
    {U₁ : B ⥤ A} {V₁ : A ⥤ B} {U₂ : D ⥤ C} {V₂ : C ⥤ D}
    (a₁ : G ⊣ K) (a₂ : F ⊣ H) (b₁ : U₂ ⊣ V₂) (b₂ : U₁ ⊣ V₁)
    (e : V₂ ⋙ K ≅ H ⋙ V₁) (σ : K ⋙ U₁ ⟶ U₂ ⋙ H)
    (hσ : (mateEquiv b₁ b₂ (TwoSquare.mk K U₂ U₁ H σ)).natTrans = e.hom) :
    (mateEquiv a₁ a₂ (TwoSquare.mk U₁ G F U₂
      ((conjugateIsoEquiv (a₁.comp b₁) (b₂.comp a₂)).symm e).hom)).natTrans = σ := by
  have h : mateEquiv a₁ a₂ (TwoSquare.mk U₁ G F U₂
      ((conjugateIsoEquiv (a₁.comp b₁) (b₂.comp a₂)).symm e).hom) =
      TwoSquare.mk K U₂ U₁ H σ := by
    apply (mateEquiv b₁ b₂).injective
    apply TwoSquare.ext
    rw [iterated_mateEquiv_conjugateEquiv, hσ]
    intro X
    change ((conjugateEquiv (a₁.comp b₁) (b₂.comp a₂))
      ((conjugateEquiv (a₁.comp b₁) (b₂.comp a₂)).symm e.hom)).app X = e.hom.app X
    exact congr_app (Equiv.apply_symm_apply _ _) X
  exact congrArg TwoSquare.natTrans h

private theorem isIso_left_mate_of_iterated
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {F : A ⥤ C} {H : C ⥤ A} {G : B ⥤ D} {K : D ⥤ B}
    (b₁ : F ⊣ H) (b₂ : G ⊣ K) (τ : U₁ ⋙ F ⟶ G ⋙ U₂)
    (hτ : IsIso ((mateEquiv b₂ b₁ (TwoSquare.mk _ _ _ _ τ)).natTrans)) :
    IsIso (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).natTrans) := by
  let δ := (mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)
  have hm : mateEquiv a₁ a₂ δ = TwoSquare.mk _ _ _ _ τ := Equiv.apply_symm_apply _ _
  have h := iterated_mateEquiv_conjugateEquiv a₁ a₂ b₁ b₂ δ
  rw [hm] at h
  have : IsIso (conjugateEquiv (a₁.comp b₂) (b₁.comp a₂) δ.natTrans) := h ▸ hτ
  exact conjugateEquiv_of_iso (a₁.comp b₂) (b₁.comp a₂) δ.natTrans

/-- A reduction boundary for the published exact square descent. Its data is exactly
that descent; the boundary prevents repeated unfolding of derived localizations.
Source: Stacks 010N (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def exactSquare
    {C₁ : Type c₁} {C₂ : Type c₂} {C₃ : Type c₃} {C₄ : Type c₄}
    [Category.{h₁} C₁] [Category.{h₂} C₂] [Category.{h₃} C₃] [Category.{h₄} C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory.{d₁} C₁] [HasDerivedCategory.{d₂} C₂]
    [HasDerivedCategory.{d₃} C₃] [HasDerivedCategory.{d₄} C₄]
    {F₁ : C₁ ⥤ C₂} {F₂ : C₂ ⥤ C₄} {G₁ : C₁ ⥤ C₃} {G₂ : C₃ ⥤ C₄}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ≅
      G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso e

/-- The prescribed coefficient-universe lift.
Source: Stacks 00YV (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev liftedHom {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    ULift.{u + 1, u} A →+* ULift.{u + 1, u} B := f.ulift

/-- Exact scalar restriction on the actual small pro-etale site.
Source: Stacks 03DA (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev fixedRestriction {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :=
  @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
    (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (liftedHom f)

/-- The fixed-module presentation of the recorded scalar extension.
Source: Stacks 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev fixedScalar {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :=
  @pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
    (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (liftedHom f)

/-- The derived realization square for restriction of scalars, with its prescribed
identity on scalar-unit sections. Source: Stacks 00YV and 03DA
(blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def restrictionPresentation
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T B).functor ⋙ scalarRestriction f T ≅
      fixedRestriction f T ⋙
        (sfIntrinsicDerivedEquivalence T A).functor :=
  exactSquare (sfRealizationRestriction T f)

/-- The scalar presentation is the left-adjoint uniqueness comparison determined by
restrictionPresentation, hence by identity on the scalar-unit sections. No arbitrary
isomorphism of scalar functors is chosen. Source: Stacks 00YV and 06YY
(blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def scalarPresentation {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T A).functor ⋙ scalarExtensionFunctor f T ≅
      fixedScalar f T ⋙ (sfIntrinsicDerivedEquivalence T B).functor :=
  let e := restrictionPresentation f T
  let rightIso :=
    isoWhiskerRight (sfIntrinsicDerivedEquivalence T B).counitIso.symm
      (scalarRestriction f T ⋙ (sfIntrinsicDerivedEquivalence T A).inverse) ≪≫
    isoWhiskerLeft (sfIntrinsicDerivedEquivalence T B).inverse
      (isoWhiskerRight e (sfIntrinsicDerivedEquivalence T A).inverse) ≪≫
    isoWhiskerLeft
      ((sfIntrinsicDerivedEquivalence T B).inverse ⋙
        fixedRestriction f T)
      (sfIntrinsicDerivedEquivalence T A).unitIso.symm
  (((sfIntrinsicDerivedEquivalence T A).toAdjunction.comp
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) f))).ofNatIsoRight
      rightIso).leftAdjointUniq
    ((Adjunction.ofIsRightAdjoint
      (fixedRestriction f T)).comp
        (sfIntrinsicDerivedEquivalence T B).toAdjunction)

/-- Cancel the realization unit in extension by zero, then descend the exact sheaf
square termwise. Source: Stacks 00YV and 03DI
(blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def openPresentation (A : Type u) [CommRing A] [Finite A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence U A).functor ⋙
        (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Z A).functor :=
  (mapDerivedCategoryCompIso _ _).symm ≪≫
    mapDerivedCategoryNatIso
      ((sfIntrinsicModuleEquivalence U A).funInvIdAssoc
        (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
          (sfIntrinsicModuleEquivalence Z A).functor)) ≪≫
    mapDerivedCategoryCompIso _ _

/-- The exact, uncompleted comparison in fixed coefficients.
Source: Stacks 099T (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev comparison (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory

/-- The open-supported etale complex K.
Source: Stacks 03DI (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev etaleOpen (A : Type u) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :=
  (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory

/-- The fixed-module coordinates of the recorded pro-etale extension by zero N.
Source: Stacks 03DI and 00YV (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev proOpen (A : Type u) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory

/-- The natural open comparison, descended termwise before taking a component.
Source: Stacks 09AF (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def openComparison (A : Type u) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    etaleOpen A j ⋙ comparison A Z ≅ comparison A U ⋙ proOpen A j :=
  exactSquare
    (openImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)

/-- The canonical identification nu K with N relative to the chosen origin e.
Source: Stacks 09AF (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def supportedComparison (A : Type u) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) U)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (e : (comparison A U).obj L ≅ M) :
    (comparison A Z).obj ((etaleOpen A j).obj L) ≅ (proOpen A j).obj M :=
  (openComparison A j).app L ≪≫ (proOpen A j).mapIso e

/-- Scalar extension with the actual small-site universes specified.
Source: Stacks 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev proFixedScalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :=
  @pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T) A B
    inferInstance inferInstance f

/-- Derived restriction with the actual small-site universes specified.
Source: Stacks 03DA (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev proFixedRestriction {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :=
  @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T) A B
    inferInstance inferInstance f

/-- B as an A-module sheaf, using actual exact restriction of scalars.
Source: Stacks 03EK (blueprint: lem-sp-supported-etale-tensor-origin). -/
def proScalarCoefficientSheaf
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj
    (𝟙_ (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))

/-- The ordinary balancing map M tensor_A B to the restricted scalar extension.
It is scalar unit, followed by the lax tensorator of restriction and the right unitor.
Source: Stacks 03EK (blueprint: lem-sp-supported-etale-tensor-origin). -/
def proScalarSheafTensorMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :
    M ⊗ proScalarCoefficientSheaf φ T ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj
        ((ProEtale.sheafExtendScalars φ T).obj M) :=
  (ProEtale.sheafExtendScalarsAdjunction φ T).unit.app M ▷
      proScalarCoefficientSheaf φ T ≫
    Functor.LaxMonoidal.μ (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
      ((ProEtale.sheafExtendScalars φ T).obj M) (𝟙_ _) ≫
    (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map (ρ_ _).hom

private theorem balancing_naturality
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [R.LaxMonoidal] (adj : L ⊣ R)
    {M N : C} (a : M ⟶ N) :
    a ▷ R.obj (𝟙_ D) ≫
        (adj.unit.app N ▷ R.obj (𝟙_ D) ≫
          Functor.LaxMonoidal.μ R (L.obj N) (𝟙_ D) ≫ R.map (ρ_ (L.obj N)).hom) =
      (adj.unit.app M ▷ R.obj (𝟙_ D) ≫
          Functor.LaxMonoidal.μ R (L.obj M) (𝟙_ D) ≫ R.map (ρ_ (L.obj M)).hom) ≫
        R.map (L.map a) := by
  have hn : a ≫ adj.unit.app N = adj.unit.app M ≫ R.map (L.map a) :=
    adj.unit.naturality a
  rw [← comp_whiskerRight_assoc, hn]
  rw [comp_whiskerRight_assoc, Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [← R.map_comp, rightUnitor_naturality, R.map_comp]
  simp only [Category.assoc]

/-- Naturality of the balancing map.
Source: Stacks 03EK (blueprint: lem-sp-supported-etale-tensor-origin).
Proof: apply naturality of the scalar unit, the lax tensorator, and the right unitor.
On sections this is (m tensor b) maps to b tensor a(m). -/
theorem proScalarSheafTensorMap_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)} (a : M ⟶ N) :
    a ▷ proScalarCoefficientSheaf φ T ≫ proScalarSheafTensorMap φ T N =
      proScalarSheafTensorMap φ T M ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map
          ((ProEtale.sheafExtendScalars φ T).map a) := by
  exact balancing_naturality (ProEtale.sheafExtendScalarsAdjunction φ T) a

/-- The ordinary balancing map, as a natural transformation.
Source: Stacks 03EK (blueprint: lem-sp-supported-etale-tensor-origin). -/
def proScalarSheafTensorTransformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    tensorRight (proScalarCoefficientSheaf φ T) ⟶
      ProEtale.sheafExtendScalars φ T ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology T) φ where
  app := proScalarSheafTensorMap φ T
  naturality _ _ a := proScalarSheafTensorMap_naturality φ T a

/-- The derived-extension counit on a cochain representative, including the quotient factor.
Source: Stacks 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
def proScalarExtensionRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    (proFixedScalar φ T).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) :=
  ((Adjunction.ofIsRightAdjoint
      (proFixedRestriction φ T)).homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex
            (ProEtale.sheafExtendScalarsAdjunction φ T).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ProEtale.sheafExtendScalars φ T ⋙
              Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)) (.up ℤ)).inv.app P) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P))

attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  proScalarCoefficientSheaf proScalarSheafTensorTransformation

section TensorComparison

set_option backward.isDefEq.respectTransparency.types false

variable {C : Type c₁} [Category.{h₁} C] [Abelian C] [IsGrothendieckAbelian.{h₁} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{h₁} C] [Abelian.HasFunctorialFlatResolution C]

private def tensorCounit (F : C) :
    DerivedCategory.Q ⋙ AlgebraicGeometry.Etale.scalarTensorModelFunctor F ⟶
      (tensorRight F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := Functor.LaxMonoidal.μ DerivedCategory.Q P
      ((HomologicalComplex.single C (.up ℤ) 0).obj F) ≫
    DerivedCategory.Q.map
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) F).hom.app P)
  naturality P R a := by
    change (DerivedCategory.Q.map a ▷ _) ≫ _ = _
    erw [Functor.LaxMonoidal.μ_natural_left_assoc]
    erw [← DerivedCategory.Q.map_comp]
    erw [(CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (curriedTensor C) F).hom.naturality a]
    erw [DerivedCategory.Q.map_comp]
    simp only [Functor.comp_map, Category.assoc]
    rfl

private theorem tensorCounit_isIso (F : C) (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    IsIso ((tensorCounit F).app P) := by
  have h : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj F))) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ))
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj F))
    ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P
      ((HomologicalComplex.single C (.up ℤ) 0).obj F)) := by
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map
        (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) P
          ((HomologicalComplex.single C (.up ℤ) 0).obj F))) ≫ _)
    infer_instance
  dsimp only [tensorCounit]
  infer_instance

private theorem tensorComparison_existsUnique (F : C) (V : C ⥤ C) [V.Additive]
    (τ : tensorRight F ≅ V) (G : DerivedCategory C ⥤ DerivedCategory C)
    (r : DerivedCategory.Q ⋙ G ⟶ V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hr : ∀ P : CochainComplex C ℤ,
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P → IsIso (r.app P))
    (r₀ : ∀ P : CochainComplex C ℤ, G.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj P))
    (hrr : ∀ P, r.app P = r₀ P) :
    ∃! e : G ≅ AlgebraicGeometry.Etale.scalarTensorModelFunctor F,
      AlgebraicGeometry.Etale.scalarTensorModelNormalization F τ.hom e r₀ := by
  let α := tensorCounit F ≫ Functor.whiskerRight
    (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)) DerivedCategory.Q
  have hα : (AlgebraicGeometry.Etale.scalarTensorModelFunctor F).IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
    apply (HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat
      |>.isLeftDerivedFunctor_of_isLeftDerivabilityStructure α
    intro P
    change IsIso (α.app P.obj)
    have := tensorCounit_isIso F P.obj P.property
    have : IsIso ((NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app P.obj) :=
      ((NatIso.mapHomologicalComplex τ (.up ℤ)).app P.obj).isIso_hom
    dsimp only [α, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  have hG : G.IsLeftDerivedFunctor r (HomologicalComplex.quasiIso C (.up ℤ)) := by
    apply (HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat
      |>.isLeftDerivedFunctor_of_isLeftDerivabilityStructure r
    exact fun P ↦ hr P.obj P.property
  let e : G ≅ AlgebraicGeometry.Etale.scalarTensorModelFunctor F :=
    Functor.leftDerivedUnique _ _ r α (HomologicalComplex.quasiIso C (.up ℤ))
  have he : AlgebraicGeometry.Etale.scalarTensorModelNormalization F τ.hom e r.app := by
    intro P
    simpa only [e, Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom, Iso.refl_hom,
      α, tensorCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      NatTrans.id_app, Category.comp_id, Category.assoc] using
      (Functor.leftDerivedNatTrans_app _ _ r α
        (HomologicalComplex.quasiIso C (.up ℤ)) (𝟙 _) P)
  refine ⟨e, fun P ↦ (he P).trans (hrr P), ?_⟩
  intro e' he'
  apply Iso.ext
  apply Functor.leftDerived_ext _ α (HomologicalComplex.quasiIso C (.up ℤ))
  ext P
  simpa only [α, tensorCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] using ((he' P).trans (hrr P).symm).trans (he P).symm

end TensorComparison

set_option backward.isDefEq.respectTransparency.types false in
/-- H is the tensor in the ordinary uncompleted etale derived category; B has its
specified A-action. Source: Stacks 07A4
(blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev etaleTensor {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) U) :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z).obj
    ((etaleOpen A j).obj L)).obj (Etale.scalarCoefficient (liftedHom f) Z)

set_option linter.unusedVariables false in
end SupportedEtaleTensorOrigin
end AlgebraicGeometry.ProEtale
