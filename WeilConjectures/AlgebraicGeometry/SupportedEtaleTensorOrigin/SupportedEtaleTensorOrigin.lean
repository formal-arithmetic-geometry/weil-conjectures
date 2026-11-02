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
public import WeilConjectures.SixFunctors.ExactRightDerivedAdjointKFlatRepresentative

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

/-- Exact restriction of the scalar-extension representative map.
Source: Stacks 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
def proScalarRestrictedExtensionRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    (proFixedRestriction φ T).obj
        ((proFixedScalar φ T).obj (_root_.DerivedCategory.Q.obj P)) ⟶
      _root_.DerivedCategory.Q.obj
        (((ProEtale.sheafExtendScalars φ T ⋙
          Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapHomologicalComplex
            (.up ℤ)).obj P) :=
  (proFixedRestriction φ T).map
      (proScalarExtensionRepresentative φ T P) ≫
    (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapDerivedCategoryFactors.hom.app
      (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) ≫
    _root_.DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (ProEtale.sheafExtendScalars φ T ⋙
          Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)) (.up ℤ)).hom.app P)

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

private theorem adjointTensorComparison
    {D : Type c₂} [Category.{h₁} D] [Abelian D] [HasDerivedCategory.{h₁} D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) (L : DerivedCategory C ⥤ DerivedCategory D)
    (ad : L ⊣ U.mapDerivedCategory) (F : C) (τ : tensorRight F ≅ E ⋙ U)
    (r₀ : ∀ P : CochainComplex C ℤ,
      (L ⋙ U.mapDerivedCategory).obj (DerivedCategory.Q.obj P) ⟶
        DerivedCategory.Q.obj (((E ⋙ U).mapHomologicalComplex (.up ℤ)).obj P))
    (hr₀ : ∀ P, r₀ P = U.mapDerivedCategory.map
        ((ad.homEquiv _ _).symm
          (DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
                (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
                (Functor.mapHomologicalComplexCompIso
                  (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P) ≫
            U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P))) ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).hom.app P)) :
    ∃! e : L ⋙ U.mapDerivedCategory ≅ Etale.scalarTensorModelFunctor F,
      Etale.scalarTensorModelNormalization F τ.hom e r₀ := by
  let η : DerivedCategory.Q ⟶
      (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙ U.mapDerivedCategory :=
    { app P := DerivedCategory.Q.map
          (((adj).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P)
      naturality P R a := by
        have hn := ((adj).mapHomologicalComplex
          (.up ℤ)).unit.naturality a
        change a ≫ _ = _ at hn
        rw [← DerivedCategory.Q.map_comp_assoc, hn]
        rw [DerivedCategory.Q.map_comp, Category.assoc]
        simpa only [Functor.comp_map, Category.assoc] using congrArg
          (fun b ↦ DerivedCategory.Q.map
            (((adj).mapHomologicalComplex
              (.up ℤ)).unit.app P) ≫ b)
          (U.mapDerivedCategoryFactors.inv.naturality
            ((E.mapHomologicalComplex (.up ℤ)).map a)) }
  let r : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    { app P := (ad.homEquiv _ _).symm (η.app P)
      naturality P R a := ad.homEquiv_naturality_right_square
        (DerivedCategory.Q.map a) (η.app R) (η.app P)
        (DerivedCategory.Q.map ((E.mapHomologicalComplex (.up ℤ)).map a)) (η.naturality a) }
  have hr (P : CochainComplex C ℤ)
      (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) : IsIso (r.app P) := by
    exact Adjunction.isIso_cochainTranspose_of_kFlat E U
      (adj) ad P hP
  let r' : DerivedCategory.Q ⋙ (L ⋙ U.mapDerivedCategory) ⟶
      (E ⋙ U).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight r U.mapDerivedCategory ≫
      Functor.whiskerLeft (E.mapHomologicalComplex (.up ℤ)) U.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).hom
        DerivedCategory.Q
  have hr' (P : CochainComplex C ℤ)
      (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) : IsIso (r'.app P) := by
    have := hr P hP
    dsimp only [r', NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have hrep (P : CochainComplex C ℤ) : r'.app P = r₀ P := by
    dsimp only [r', r, η, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    have hu : (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
        (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
      ext i
      simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
        HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
        NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
        Iso.refl_inv, NatTrans.id_app, Category.id_comp]
      change adj.unit.app (P.X i) = adj.unit.app (P.X i) ≫ 𝟙 _
      exact (Category.comp_id _).symm
    rw [hu]
    exact (hr₀ P).symm
  exact tensorComparison_existsUnique F (E ⋙ U) τ (L ⋙ U.mapDerivedCategory) r' hr' r₀ hrep

/-- The pro-etale scalar/tensor isomorphism is uniquely fixed by the exact same
representative normalization as its etale counterpart. Source: Stacks 06YY and 03EK
(blueprint: lem-sp-supported-etale-tensor-origin).
Proof: on a K-flat representative, the balancing map identifies the tensor with the
underlying scalar-extension complex. The left-derived counit computes scalar extension;
Q's lax tensorator and the single-complex totalization compute the tensor. These give
the stated equation. Naturality with respect to a K-flat resolution extends it to every
complex and determines the natural isomorphism uniquely after localization. -/
theorem proScalarTensorIso_existsUnique
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    ∃! e : proFixedScalar f T ⋙
        proFixedRestriction f T ≅
          Etale.scalarTensorModelFunctor (proScalarCoefficientSheaf f T),
      Etale.scalarTensorModelNormalization (proScalarCoefficientSheaf f T)
        (proScalarSheafTensorTransformation f T) e
        (proScalarRestrictedExtensionRepresentative f T) := by
  let := f.toAlgebra
  let E := ProEtale.sheafExtendScalars f T
  let U := Sheaf.restrictScalars (Scheme.ProEt.topology T) f
  let ad : proFixedScalar f T ⊣ proFixedRestriction f T :=
    Adjunction.ofIsRightAdjoint (proFixedRestriction f T)
  have : E.PreservesKFlatQuasiIso :=
    inferInstanceAs ((ProEtale.sheafExtendScalars (algebraMap A B) T).PreservesKFlatQuasiIso)
  have : PreservesFiniteLimits U := by
    let := (ProEtale.sheafExtendScalarsAdjunction f T).rightAdjoint_preservesLimits
    infer_instance
  have : PreservesFiniteColimits U := by
    let :=
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) f).leftAdjoint_preservesColimits
    infer_instance
  have hτ : IsIso (proScalarSheafTensorTransformation f T) := by
    exact inferInstanceAs (IsIso (ProEtale.sheafExtendScalarsProjection A B T))
  apply adjointTensorComparison E U (ProEtale.sheafExtendScalarsAdjunction f T)
    (proFixedScalar f T) ad (proScalarCoefficientSheaf f T)
    (asIso (proScalarSheafTensorTransformation f T))
    (proScalarRestrictedExtensionRepresentative f T)
  intro P
  rfl

/-- The unique normalized pro-etale scalar/tensor comparison.
Source: Stacks 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def proScalarTensorIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    proFixedScalar f T ⋙ proFixedRestriction f T ≅
      Etale.scalarTensorModelFunctor (proScalarCoefficientSheaf f T) :=
  (proScalarTensorIso_existsUnique f T).exists.choose

/-- The scalar/open comparison is the mate of the exact restriction square. Its
invertibility is asserted in the main theorem, rather than chosen as arbitrary data.
Source: Stacks 03DI and 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
def openScalarMap {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :=
  ((mateEquiv
    (G := proOpen A j) (H := proOpen B j)
    (Adjunction.ofIsRightAdjoint (fixedRestriction f U))
    (Adjunction.ofIsRightAdjoint (fixedRestriction f Z))).symm
    (TwoSquare.mk _ _ _ _
      (exactSquare (sfFixedOpenRestriction j f)).hom)).natTrans

private theorem open_restrict_coextend_mate
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    (mateEquiv
      (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Z) (liftedHom f))
      (Sheaf.restrictCoextendScalarsAdj (ProEt.topology U) (liftedHom f))
      (TwoSquare.mk _ _ _ _
        (show ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j ⋙
            Sheaf.restrictScalars (ProEt.topology U) (liftedHom f) ⟶
          Sheaf.restrictScalars (ProEt.topology Z) (liftedHom f) ⋙
            ProEtale.openImmersionRestriction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j from 𝟙 _))).natTrans =
      𝟙 _ := by
  ext F V x
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app,
    Category.id_comp]
  let V' : Z.ProEtᵒᵖ := (MorphismProperty.Over.map ⊤
    (show WeaklyEtale j from inferInstance)).op.obj V
  change (((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
      (liftedHom f)).unit.app
      ((ModuleCat.coextendScalars.{u + 1, u + 1, u + 1}
        (liftedHom f)).obj (F.obj.obj V'))) ≫
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} (liftedHom f)).map
        ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
          (liftedHom f)).counit.app (F.obj.obj V'))).hom x = x
  have h := (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
    (liftedHom f)).right_triangle_components (F.obj.obj V')
  exact congrArg (fun a ↦ a.hom x) h

private theorem open_restrict_mate
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    (mateEquiv
      (ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
      (ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
      (TwoSquare.mk _ _ _ _ (sfFixedOpenRestriction j f).hom)).natTrans = 𝟙 _ := by
  exact mate_of_conjugate
    (ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
    (ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Z) (liftedHom f))
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology U) (liftedHom f))
    (Iso.refl _) (𝟙 _) (open_restrict_coextend_mate f j)

private theorem openScalarMap_isIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    IsIso (openScalarMap f j) := by
  let := (ProEtale.openImmersionRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).isLeftAdjoint
  let := (ProEtale.openImmersionRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).isLeftAdjoint
  let bA := ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let bB := ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j
  let τ : ProEtale.openImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j ⋙
        Sheaf.restrictScalars (ProEt.topology U) (liftedHom f) ≅
      Sheaf.restrictScalars (ProEt.topology Z) (liftedHom f) ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j :=
    Iso.refl _
  have hβ : ∀ K, bA.unit.app
        ((Sheaf.restrictScalars (ProEt.topology U) (liftedHom f)).obj K) ≫
      (ProEtale.openImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
        ((sfFixedOpenRestriction j f).hom.app K) =
      (Sheaf.restrictScalars (ProEt.topology U) (liftedHom f)).map (bB.unit.app K) ≫
        τ.hom.app ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).obj K) := by
    intro K
    have h := unit_mateEquiv bB bA
      (TwoSquare.mk _ _ _ _ (sfFixedOpenRestriction j f).hom) K
    change _ ≫ (mateEquiv bB bA _).natTrans.app _ = _ at h
    rw [open_restrict_mate] at h
    exact h.symm
  have hβd := bB.mapDerivedCategoryAdjunction_mate bA τ
    (sfFixedOpenRestriction j f) hβ
  dsimp only [openScalarMap]
  apply isIso_left_mate_of_iterated
    (Adjunction.ofIsRightAdjoint (fixedRestriction f U))
    (Adjunction.ofIsRightAdjoint (fixedRestriction f Z))
    bA.mapDerivedCategoryAdjunction bB.mapDerivedCategoryAdjunction
  have hs : TwoSquare.mk _ _ _ _ (exactSquare (sfFixedOpenRestriction j f)).hom =
      (mateEquiv bB.mapDerivedCategoryAdjunction bA.mapDerivedCategoryAdjunction).symm
        (TwoSquare.mk _ _ _ _ (exactSquare τ).hom) := by
    unfold exactSquare
    apply TwoSquare.ext
    intro K
    apply (bA.mapDerivedCategoryAdjunction.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit]
    exact (hβd K).trans
      (unit_mateEquiv_symm bB.mapDerivedCategoryAdjunction
        bA.mapDerivedCategoryAdjunction
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso τ).hom) K)
  rw [hs, Equiv.apply_symm_apply]
  infer_instance

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

/-- The etale scalar/tensor family with the existing representative normalization.
Source: Stacks 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def etaleScalarTensorFamily {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    Etale.scalarExtension f T ⋙ Sheaf.derivedRestrictScalars T.smallEtaleTopology f ≅
      (Etale.derivedTensor (ModuleCat.{u + 1} A) T).flip.obj (Etale.scalarCoefficient f T) :=
  (Etale.scalarTensorIso_existsUnique f T).exists.choose

/-- Compose the normalized scalar, restriction and tensor squares before taking
components. This formula is purely functorial and avoids repeated localization expansion.
Source: Stacks 07A4 and 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def tensorScalarSquare
    {C₁ : Type c₁} {C₂ : Type c₂} {C₃ : Type c₃} {C₄ : Type c₄}
    [Category.{h₁} C₁] [Category.{h₂} C₂] [Category.{h₃} C₃] [Category.{h₄} C₄]
    {F : C₁ ⥤ C₃} {G : C₂ ⥤ C₄} {S : C₁ ⥤ C₂} {T : C₃ ⥤ C₄}
    {R : C₂ ⥤ C₁} {Q : C₄ ⥤ C₃} {V : C₁ ⥤ C₁} {W : C₃ ⥤ C₃}
    (e : S ⋙ R ≅ V) (r : G ⋙ Q ≅ R ⋙ F) (s : F ⋙ T ≅ S ⋙ G)
    (t : T ⋙ Q ≅ W) : V ⋙ F ≅ F ⋙ W :=
  isoWhiskerRight e.symm F ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft S r.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight s.symm Q ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft F t

/-- The normalized scalar-comparison mate, sealed for arbitrary fixed rings.
Source: Stacks 07A4 (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def fixedScalarComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (Z : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory ⋙ proFixedScalar f Z ≅
      Etale.scalarExtension f Z ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} B) Z).mapDerivedCategory :=
  pbcComparisonReduction Z f

/-- Restriction comparison, before specializing the rings or taking components.
Source: Stacks 03DA (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def fixedRestrictionComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (Z : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} B) Z).mapDerivedCategory ⋙ proFixedRestriction f Z ≅
      Sheaf.derivedRestrictScalars Z.smallEtaleTopology f ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory :=
  pbcDerivedComparisonRestrict Z f

/-- The canonical tensor square uses the generic scalar-comparison composition.
Source: Stacks 07A4 and 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev fixedTensorComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (Z : Scheme.{u}) :=
  tensorScalarSquare (etaleScalarTensorFamily f Z) (fixedRestrictionComparison f Z)
    (fixedScalarComparison f Z) (proScalarTensorIso f Z)

/-- Compose scalar restriction after the open scalar mate in fixed coordinates.
Source: Stacks 0GL1 and 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
def supportedFixedScalarMap {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :=
  whiskerLeft (proOpen A j) (proScalarTensorIso (liftedHom f) Z).inv ≫
    whiskerRight (openScalarMap f j) (fixedRestriction f Z)

/-- The same specified scalar arrow with the actual recorded intrinsic target:
Res j!_B T_U(M). The three boundary comparisons are normalized by scalar sections
and adjunction units. Source: Stacks 00YV, 03DI, 06YY
(blueprint: lem-sp-supported-etale-tensor-origin). -/
def supportedIntrinsicScalarMap
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :=
  whiskerRight (supportedFixedScalarMap f j) (sfIntrinsicDerivedEquivalence Z A).functor ≫
    whiskerLeft (fixedScalar f U ⋙ proOpen B j) (restrictionPresentation f Z).inv ≫
    whiskerLeft (fixedScalar f U)
      (whiskerRight (openPresentation B j).inv (scalarRestriction f Z)) ≫
    whiskerRight (scalarPresentation f U).inv
      ((sfIntrinsicExtensionByZero j B).mapDerivedCategory ⋙ scalarRestriction f Z)

/-- A bounded intrinsically constructible finite-Tor complex has an etale origin
whose supported coefficient tensor is bounded, with the specified canonical comparisons.
Source: blueprint main-20261015, sk-lem-sp-reduction-direct-image.proof.md, Step 1;
Stacks 09AK, 09AL, 09AF, 07A4, 08FZ, 0GL1 and 099T
(blueprint: lem-sp-supported-etale-tensor-origin).

Proof: apply lem-weil-pbc-finite-ring-constructible-sheaf-origin to each cohomology
sheaf. The bounded-origin theorem lem-weil-pbc-fixed-module-bounded-constructible-origin
then gives L and e, without a Noetherian hypothesis on U. Exact etale and pro-etale
extension by zero commute with cohomology, so K and N are bounded. The exact open
comparison, descended termwise and composed with e, is supportedComparison.
The unbounded monoidal comparison and the constant B coefficient comparison give
fixedTensorComparison before boundedness of H is known. Choose [a,b] witnessing
the finite Tor amplitude of M. Testing against B_U bounds M tensor B_U in this interval;
no Tor bound on B is used. The open projection formula of
lem-cbc-extension-zero-projection-formula identifies N tensor B_Z with its exact
extension by zero. On a K-flat resolution scalar extension has this same tensor complex
with its B-action; forgetting that action is the normalized scalar/tensor identification.
The exact restriction square for extension by zero yields the isomorphism whose
canonical arrow is supportedIntrinsicScalarMap. The displayed mate and realization comparisons
preserve the adjunction units, so this is the same arrow, relative to e. Thus nu H is
bounded in [a,b]. Exact faithful comparison commutes with cohomology and reflects zero
objects, hence H itself is bounded in [a,b]. Bounded K and H in particular lie in D+.
The zero ring and zero complex require no exception. -/
theorem supported_etale_tensor_origin
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B)
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0) (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hM : _root_.DerivedCategory.TStructure.t.bounded M)
    (hc : ∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf U (ULift.{u + 1, u} A)
      ((_root_.DerivedCategory.homologyFunctor _ q).obj M))
    (ht : HasFiniteProEtaleTorAmplitude U A
      ((sfIntrinsicDerivedEquivalence U A).functor.obj M)) :
    ∃ L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) U,
      _root_.DerivedCategory.TStructure.t.bounded L ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj L)) ∧
      ∃ e : (comparison A U).obj L ≅ M,
        _root_.DerivedCategory.TStructure.t.bounded ((etaleOpen A j).obj L) ∧
        _root_.DerivedCategory.TStructure.t.bounded (etaleTensor f j L) ∧
        _root_.DerivedCategory.TStructure.t.plus ((etaleOpen A j).obj L) ∧
        _root_.DerivedCategory.TStructure.t.plus (etaleTensor f j L) ∧
        IsIso ((supportedIntrinsicScalarMap f j).app M) := by
  obtain ⟨⟨L, hL, hcL, ⟨e⟩⟩, hOpen⟩ :=
    SupportedConstructibleOriginComparison.supported_constructible_origin_comparison
      (ULift.{u + 1, u} A) j M hM hc
  have hK := (hOpen L hL hcL e).1
  obtain ⟨a, b, ht⟩ := ht
  have htM := (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A U a b ht.1 M).mp ht
  have htN := torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek j htM
  have htK := (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
    (Λ := ULift.{u + 1, u} A) a b ((etaleOpen A j).obj L)).mp
      ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
        (supportedComparison A j L M e).symm htN)
  have hH : _root_.DerivedCategory.TStructure.t.bounded (etaleTensor f j L) := by
    exact (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).mp
      ⟨a, b, htK (Etale.scalarCoefficientSheaf (liftedHom f) Z)⟩
  refine Exists.intro L (And.intro hL (And.intro hcL ?_))
  refine Exists.intro e (And.intro hK (And.intro hH (And.intro hK.1 (And.intro hH.1 ?_))))
  have := openScalarMap_isIso f j
  dsimp only [supportedIntrinsicScalarMap, supportedFixedScalarMap]
  infer_instance

set_option linter.unusedVariables false in
end SupportedEtaleTensorOrigin
end AlgebraicGeometry.ProEtale
