/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules

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
  sorry

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
  sorry

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
  sorry

end SupportedEtaleTensorOrigin
end AlgebraicGeometry.ProEtale
