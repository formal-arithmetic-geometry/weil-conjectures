/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q147
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
import all Sheaf.Paper.IntegralDerivedOperationsOnSlices
import all Sheaf.Paper.IntegralOperationsWellDefined

/-!
# Ordinary and completed integral pullback

Source: Bhatt--Scholze, Lemma 6.5.9, Proposition 6.6.11 and Remark 6.8.15;
Stacks Project, Tags 06YY and 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback).

The ordinary pullback uses the adjoint of the completed coefficient map fixed by
all finite projections. The comparison is fixed on flat-term K-flat representatives
by the quotient augmentation and the zero second coordinate of the strict Roos cone.

## Main definitions

* `ordinaryIntegralDerivedPull`: ordinary unbounded ringed pullback before completion.
* `ordinaryIntegralCompletionChain`: the prescribed (quotients, zero) cone map.
* `ordinaryIntegralCompletionComparison`: its uniquely normalized derived descent.

## Main statements

* `ordinaryCompletedIntegralPullback`: constructibility and invertibility of this comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The finite constant coefficient map adjoint to the constant-section inverse-image map.
Source: Stacks 0H7J (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralFiniteDirectRingMap (n : ℕ) :
    integralCoefficientSheaf l E Y n ⟶
      (proEtaleSheafDirectImage f RingCat.{u + 1}).obj (integralCoefficientSheaf l E X n) :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (coefficientProEtaleDirectRingMap.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

private theorem ordinaryConstantUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) (U : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U ≫
      (coefficientProEtaleDirectRingMap.{u, u} f A).hom.app U =
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((proEtaleBaseChange f).op.obj U) := by
  have h := (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{u + 1}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A))
      |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun α ↦ α.app U) h

private theorem ordinaryConstantMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
      coefficientProEtaleDirectRingMap.{u, u} f B =
    coefficientProEtaleDirectRingMap.{u, u} f A ≫
      ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  apply (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{u + 1}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj B)) |>.injective
  apply NatTrans.ext
  funext U
  change _ ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  have hY := congrArg (fun α ↦ α.app U)
    (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a))
  change a ≫ _ = _ ≫ _ at hY
  erw [← Category.assoc, ← hY, Category.assoc, ordinaryConstantUnit,
    ← Category.assoc, ordinaryConstantUnit]
  exact congrArg (fun α ↦ α.app ((proEtaleBaseChange f).op.obj U))
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))

attribute [local irreducible] constantSheaf HasDerivedCategory.standard

/-- The adjoint completed ring map is uniquely determined by all its quotient projections.
Its inverse-image adjoint is exactly c_f of the statement.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 06YY
(blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the constant-section maps commute with quotient transitions, by their
sheafification universal property. Right adjoint direct image preserves limits.
The limit universal property supplies the displayed map and proves uniqueness. -/
theorem ordinaryIntegralDirectRingMap_existsUnique :
    ∃! ρ : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
        (proEtaleSheafDirectImage f RingCat.{u + 1}).obj
          (completedIntegralCoefficientSheafUnrestricted l E X),
      ∀ n : ℕ, ρ ≫ (proEtaleSheafDirectImage f RingCat.{u + 1}).map
          (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
        limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫
          ordinaryIntegralFiniteDirectRingMap l E f n := by
  let G := proEtaleSheafDirectImage f RingCat.{u + 1}
  let τ : integralCoefficientSheafSystem l E Y ⟶
      integralCoefficientSheafSystem l E X ⋙ G :=
    NatTrans.ofOpSequence (ordinaryIntegralFiniteDirectRingMap l E f) (fun n ↦ by
      simp only [integralCoefficientSheafSystem, Functor.comp_map,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact congrArg
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
        (ordinaryConstantMap_naturality f
          (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift)))
  let c : Cone (integralCoefficientSheafSystem l E X ⋙ G) :=
    { pt := completedIntegralCoefficientSheafUnrestricted l E Y
      π := (limit.cone (integralCoefficientSheafSystem l E Y)).π ≫ τ }
  let hc := isLimitOfPreserves G (limit.isLimit (integralCoefficientSheafSystem l E X))
  refine ⟨hc.lift c, ?_, ?_⟩
  · intro n
    exact hc.fac c (op n)
  · intro ρ hρ
    apply hc.hom_ext
    intro n
    exact (hρ n.unop).trans (hc.fac c n).symm

attribute [local irreducible] limit

/-- The canonical completed coefficient map, in its direct-image adjoint form.
Source: Bhatt--Scholze, Lemma 6.5.9
(blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralDirectRingMap :=
  (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose

attribute [local irreducible] ordinaryIntegralDirectRingMap

/-- The actual sectionwise module direct image with this completed coefficient action.
Source: Stacks 03D1 (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralModulePush : integralTowerModules l E X ⥤ integralTowerModules l E Y :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (ordinaryIntegralDirectRingMap l E f)

/-- The specified pushforward has the sheafified module Kan-extension left adjoint.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: transport to the already recorded small site models, form the presheaf
module Kan extension along the displayed ring map and sheafify. Transport its
adjunction back. Its right adjoint is the specified sectionwise module pushforward.
The left adjoint is B_X tensor over f-inverse B_Y with f-inverse of the module. -/
@[instance] theorem ordinaryIntegralModulePush_isRightAdjoint :
    (ordinaryIntegralModulePush l E f).IsRightAdjoint := by
  exact SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u}
    (U := proEtaleBaseChange f) (ordinaryIntegralDirectRingMap l E f)

/-- Ordinary ringed module pullback, fixed by its sheafified Kan-extension adjunction.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralModulePull :
    integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  letI : (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
      (J := ProEt.topology Y) (K := ProEt.topology X)
      (ordinaryIntegralDirectRingMap l E f)).IsRightAdjoint :=
    ordinaryIntegralModulePush_isRightAdjoint l E f
  SheafOfModules.pullback.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (ordinaryIntegralDirectRingMap l E f)

/-- The adjunction supplying the canonical tensor generators of ordinary pullback.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralModuleAdjunction :
    ordinaryIntegralModulePull l E f ⊣ ordinaryIntegralModulePush l E f :=
  letI : (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
      (J := ProEt.topology Y) (K := ProEt.topology X)
      (ordinaryIntegralDirectRingMap l E f)).IsRightAdjoint :=
    ordinaryIntegralModulePush_isRightAdjoint l E f
  SheafOfModules.pullbackPushforwardAdjunction (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (ordinaryIntegralDirectRingMap l E f)

/-- Additivity of ordinary module pullback.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: sectionwise pushforward is additive. Its adjunction makes its left adjoint
additive by the preadditive adjunction criterion. -/
@[instance] theorem ordinaryIntegralModulePull_additive :
    (ordinaryIntegralModulePull l E f).Additive := by
  have : (ordinaryIntegralModulePush l E f).Additive := by
    refine ⟨?_⟩
    intro M N a b
    rfl
  exact (ordinaryIntegralModuleAdjunction l E f).left_adjoint_additive

attribute [local irreducible] ordinaryIntegralModulePull

/-- The canonical total left derived functor exists on the unbounded category.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: use lem-pc-kflat-resolution with independent site and coefficient sizes.
Exact inverse image followed by extension of scalars preserves quasi-isomorphisms
between flat-term K-flat complexes, by ringed-topoi-derived-pullback. Localization
of this resolving class gives the total left derived functor and its counit. -/
@[instance] theorem ordinaryIntegralPull_hasLeftDerived :
    ((ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)) := by
  sorry

/-- Ordinary unbounded derived ringed pullback, before completion.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralDerivedPull :=
  ((ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ))

/-- The counit of the specified ordinary total derived pullback.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralPullCounit :
    DerivedCategory.Qh ⋙ ordinaryIntegralDerivedPull l E f ⟶
      (ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  ((ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ))

/-- Termwise ordinary pullback on cochain representatives.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralPullComplex :=
  (ordinaryIntegralModulePull l E f).mapHomologicalComplex (.up ℤ)

/-- The ordinary computation map on a cochain representative, retaining its universal counit.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralPullComplexCounit (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralDerivedPull l E f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((ordinaryIntegralPullComplex l E f).obj P) :=
  (ordinaryIntegralDerivedPull l E f).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (ordinaryIntegralPullCounit l E f).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((ordinaryIntegralModulePull l E f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app ((ordinaryIntegralPullComplex l E f).obj P)

/-- The ordinary computation map is invertible on every flat-term K-flat representative.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the resolving-class derived-pullback theorem computes the total left derived
functor on precisely these complexes. Its counit is invertible there. The remaining
factors are the canonical cochain-to-homotopy localization isomorphisms. -/
theorem ordinaryIntegralPullComplexCounit_isIso
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    IsIso (ordinaryIntegralPullComplexCounit l E f P.obj) := by
  sorry

/-- The quotient maps, as one natural map of strict towers, are uniquely fixed on generators.
The formula is 1 tensor q ↦ 1 tensor (q tensor 1); completed linearity gives
b tensor q ↦ 1 tensor (q tensor pi_n(b)) on every inverse-image generator.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 06YY, 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the completed coefficient map commutes with each quotient by its defining
projection equation. Thus the displayed map is balanced, linear and restriction
compatible. Sheafification gives the module maps; applying them degreewise gives
chain maps. Coefficient reduction preserves one, so consecutive transition squares
commute. The same generator equality proves naturality. Locally the scalar multiples
of restrictions of adjunction-unit generators generate pullback, giving uniqueness. -/
theorem ordinaryIntegralQuotientAugmentation_existsUnique :
    ∃! a : ordinaryIntegralPullComplex l E f ⋙
        (Functor.const ℕᵒᵖ : CochainComplex (integralTowerModules l E X) ℤ ⥤ _) ⟶
      integralOperationsPullbackTowerFunctor l E f,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
        (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
        (((a.app P).app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj V))
          (((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app (op V) x) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
          (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
  sorry

/-- The actual quotient augmentation, with all quotient transitions retained.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralQuotientAugmentation :=
  (ordinaryIntegralQuotientAugmentation_existsUnique l E f).exists.choose

/-- The product of the specified quotient maps.
Source: Stacks 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralProductAugmentation
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralPullComplex l E f).obj P ⟶
      ∏ᶜ (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n)) :=
  Pi.lift (fun n ↦ ((ordinaryIntegralQuotientAugmentation l E f).app P).app (op n))

private theorem ordinaryTowerAugmentation_zero
    (M : Type*) [Category* M] [Abelian M] [HasCountableProducts M]
    (S : ℕᵒᵖ ⥤ CochainComplex M ℤ) (C : CochainComplex M ℤ)
    (a : (Functor.const ℕᵒᵖ).obj C ⟶ S) :
    Pi.lift (fun n : ℕ ↦ a.app (op n)) ≫
      towerTransitionEndomorphism (K := fun n : ℕ ↦ S.obj (op n))
        (integralOperationsTowerStep S) = 0 := by
  apply Pi.hom_ext
  intro n
  have h := a.naturality (homOfLE (Nat.le_succ n)).op
  simpa [towerTransitionEndomorphism, towerProductShift,
    integralOperationsTowerStep, Category.assoc] using sub_eq_zero.mpr h

/-- The strict quotient augmentation is killed by 1-s, with zero second cone cochain.
Source: Stacks 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: after every product projection, the composite with 1-s is the difference
between consecutive quotient maps and is zero by the strict tower's naturality.
The differential of the zero cochain is zero. Product projections are jointly monic. -/
theorem ordinaryIntegralCompletionChain_condition
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain ((ordinaryIntegralPullComplex l E f).obj P)
        (∏ᶜ fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (ordinaryIntegralProductAugmentation l E f P ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦
              ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
            (integralOperationsTowerStep
              ((integralOperationsPullbackTowerFunctor l E f).obj P))) = 0 := by
  have hzero : ordinaryIntegralProductAugmentation l E f P ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
        (integralOperationsTowerStep
          ((integralOperationsPullbackTowerFunctor l E f).obj P)) = 0 := by
    exact ordinaryTowerAugmentation_zero (integralTowerModules l E X)
      ((integralOperationsPullbackTowerFunctor l E f).obj P)
      ((ordinaryIntegralPullComplex l E f).obj P)
      ((ordinaryIntegralQuotientAugmentation l E f).app P)
  simp only [CochainComplex.HomComplex.δ_zero, zero_add, hzero,
    CochainComplex.HomComplex.Cochain.ofHom_zero]


/-- The prescribed chain map into Cone(1-s)[-1]: quotient maps and zero, respectively.
Source: Stacks 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralCompletionChain
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralPullComplex l E f).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E f).obj P :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
      (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P)))
    (ordinaryIntegralProductAugmentation l E f P) 0
    (ordinaryIntegralCompletionChain_condition l E f P)

attribute [local irreducible] towerTransitionEndomorphism

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinaryRoosLift_natural (M : Type*) [Category* M] [Abelian M]
    [HasCountableProducts M] {C D : CochainComplex M ℤ}
    {S T : ℕᵒᵖ ⥤ CochainComplex M ℤ} (a : S ⟶ T) (α : C ⟶ D)
    (u : C ⟶ ∏ᶜ fun n : ℕ ↦ S.obj (op n))
    (v : D ⟶ ∏ᶜ fun n : ℕ ↦ T.obj (op n))
    (hu : u ≫ towerTransitionEndomorphism (K := fun n : ℕ ↦ S.obj (op n))
        (integralOperationsTowerStep S) = 0)
    (hv : v ≫ towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
        (integralOperationsTowerStep T) = 0)
    (hn : α ≫ v = u ≫ Limits.Pi.map (f := fun n : ℕ ↦ S.obj (op n))
      (g := fun n : ℕ ↦ T.obj (op n)) (fun n ↦ a.app (op n))) :
    α ≫ CochainComplex.mappingCocone.lift
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
        (integralOperationsTowerStep T)) v 0 (by simp [hv]) =
      CochainComplex.mappingCocone.lift
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ S.obj (op n))
        (integralOperationsTowerStep S)) u 0 (by simp [hu]) ≫
          integralOperationsRoosMap a := by
  unfold integralOperationsRoosMap
  rw [arrowConeMap]
  exact completedCoconeLift_natural M _ _ _ _ (integralOperationsRoos_square a)
    α u v hu hv hn

private theorem ordinaryIntegralCompletionChain_natural
    {P Q : CochainComplex (integralTowerModules l E Y) ℤ} (a : P ⟶ Q) :
    (ordinaryIntegralPullComplex l E f).map a ≫ ordinaryIntegralCompletionChain l E f Q =
      ordinaryIntegralCompletionChain l E f P ≫
        (integralOperationsPullbackComplexFunctor l E f).map a := by
  have hn : (ordinaryIntegralPullComplex l E f).map a ≫
      ordinaryIntegralProductAugmentation l E f Q =
    ordinaryIntegralProductAugmentation l E f P ≫
      Limits.Pi.map
        (f := fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
        (g := fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj Q).obj (op n))
        (fun n ↦ ((integralOperationsPullbackTowerFunctor l E f).map a).app (op n)) := by
    apply Pi.hom_ext
    intro n
    have h := congrArg (fun k ↦ k.app (op n))
      ((ordinaryIntegralQuotientAugmentation l E f).naturality a)
    simpa [ordinaryIntegralProductAugmentation, Category.assoc] using h
  have hz (P : CochainComplex (integralTowerModules l E Y) ℤ) :
      ordinaryIntegralProductAugmentation l E f P ≫
        towerTransitionEndomorphism
          (K := fun n : ℕ ↦
            ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
          (integralOperationsTowerStep
            ((integralOperationsPullbackTowerFunctor l E f).obj P)) = 0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa only [CochainComplex.HomComplex.δ_zero, zero_add,
      CochainComplex.HomComplex.Cochain.ofHom_zero] using
      ordinaryIntegralCompletionChain_condition l E f P
  exact ordinaryRoosLift_natural (integralTowerModules l E X)
    (S := (integralOperationsPullbackTowerFunctor l E f).obj P)
    (T := (integralOperationsPullbackTowerFunctor l E f).obj Q)
    ((integralOperationsPullbackTowerFunctor l E f).map a)
    ((ordinaryIntegralPullComplex l E f).map a)
    (ordinaryIntegralProductAugmentation l E f P)
    (ordinaryIntegralProductAugmentation l E f Q) (hz P) (hz Q) hn

attribute [local irreducible] ordinaryIntegralCompletionChain
  integralOperationsPullbackComplexFunctor integralDerivedPullback integralDerivedPullbackComparison

private theorem ordinaryNormalizedComparison_existsUnique
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (p : A ⥤ B) (ff : ((Functor.whiskeringLeft A B C).obj p).FullyFaithful)
    (O F : B ⥤ C) (G : A ⥤ C) (e : p ⋙ F ≅ G) (β : p ⋙ O ⟶ G) :
    ∃! η : O ⟶ F, ∀ P, η.app (p.obj P) ≫ e.hom.app P = β.app P := by
  let α := β ≫ e.inv
  let η := ff.preimage α
  have hη : Functor.whiskerLeft p η = α := ff.map_preimage α
  refine ⟨η, ?_, ?_⟩
  · intro P
    have h := NatTrans.congr_app hη P
    change η.app (p.obj P) = β.app P ≫ e.inv.app P at h
    rw [h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  · intro η' hη'
    apply ff.map_injective
    ext P
    apply (cancel_mono (e.hom.app P)).1
    have h := NatTrans.congr_app hη P
    change η.app (p.obj P) = β.app P ≫ e.inv.app P at h
    change η'.app (p.obj P) ≫ e.hom.app P = η.app (p.obj P) ≫ e.hom.app P
    rw [hη', h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private def ordinaryIntegralComparisonOnGood :
    { β : integralOperationsGoodLocalization l E Y ⋙ ordinaryIntegralDerivedPull l E f ⟶
        integralOperationsPullbackOnGood l E f //
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        β.app P = ordinaryIntegralPullComplexCounit l E f P.obj ≫
          DerivedCategory.Q.map (ordinaryIntegralCompletionChain l E f P.obj) } := by
  let c : DerivedCategory.Q ⋙ ordinaryIntegralDerivedPull l E f ⟶
      ordinaryIntegralPullComplex l E f ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
        (ordinaryIntegralDerivedPull l E f) ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ _)
        (ordinaryIntegralPullCounit l E f) ≫
      Functor.whiskerRight
        ((ordinaryIntegralModulePull l E f).mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft (ordinaryIntegralPullComplex l E f)
        (DerivedCategory.quotientCompQhIso _).hom
  refine ⟨Functor.whiskerLeft (integralOperationsGoodComplex l E Y).ι c ≫
    { app := fun P ↦ DerivedCategory.Q.map (ordinaryIntegralCompletionChain l E f P.obj)
      naturality := by
        intro P Q a
        change DerivedCategory.Q.map ((ordinaryIntegralPullComplex l E f).map a.hom) ≫ _ =
          _ ≫ DerivedCategory.Q.map
            ((integralOperationsPullbackComplexFunctor l E f).map a.hom)
        simpa only [← Functor.map_comp] using
          congrArg DerivedCategory.Q.map
            (ordinaryIntegralCompletionChain_natural l E f a.hom) }, ?_⟩
  intro P
  change c.app P.obj ≫ _ = (_ ≫ _ ≫ _ ≫ _) ≫ _
  dsimp only [c, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj]

attribute [local irreducible] ordinaryIntegralComparisonOnGood

/-- The specified chain maps descend to a unique natural transformation.
Source: Stacks 06YY, 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the augmentation is natural on chain maps. Its strict cone map has a zero
second coordinate, so its naturality holds as chain maps, not just on projections.
Both representative constructions invert quasi-isomorphisms on the flat-term
K-flat class by ringed-topoi-derived-pullback and integral-operations-well-defined.
The resolving-class localization therefore descends the comparison. Its restriction
on that class is faithful, proving uniqueness and independence of the resolution. -/
theorem ordinaryIntegralCompletionComparison_existsUnique :
    ∃! η : ordinaryIntegralDerivedPull l E f ⟶ integralDerivedPullback l E f,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        η.app (DerivedCategory.Q.obj P.obj) ≫
            (integralDerivedPullbackComparison l E f).hom.app P =
          ordinaryIntegralPullComplexCounit l E f P.obj ≫
            DerivedCategory.Q.map (ordinaryIntegralCompletionChain l E f P.obj) := by
  let L := integralOperationsGoodLocalization l E Y
  let O := ordinaryIntegralDerivedPull l E f
  let F := integralDerivedPullback l E f
  let e := integralDerivedPullbackComparison l E f
  let β := (ordinaryIntegralComparisonOnGood l E f).val
  let ff := Classical.choice (good_whisker_fullyFaithful l E Y
    (DerivedCategory (integralTowerModules l E X)))
  have h := ordinaryNormalizedComparison_existsUnique L ff O F _ e β
  change ∃! η : ordinaryIntegralDerivedPull l E f ⟶ integralDerivedPullback l E f,
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      η.app (DerivedCategory.Q.obj P.obj) ≫
        (integralDerivedPullbackComparison l E f).hom.app P =
          (ordinaryIntegralComparisonOnGood l E f).val.app P at h
  obtain ⟨η, hη, hη_unique⟩ := h
  refine ⟨η, ?_, ?_⟩
  · intro P
    exact (hη P).trans ((ordinaryIntegralComparisonOnGood l E f).property P)
  · intro η' hη'
    apply hη_unique η'
    intro P
    exact (hη' P).trans ((ordinaryIntegralComparisonOnGood l E f).property P).symm

/-- The canonical completion comparison, uniquely fixed by the (quotients,0) chain map.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralCompletionComparison :
    ordinaryIntegralDerivedPull l E f ⟶ integralDerivedPullback l E f :=
  (ordinaryIntegralCompletionComparison_existsUnique l E f).exists.choose

attribute [local irreducible] ordinaryIntegralCompletionComparison

/-- Ordinary pullback of an integral constructible object is constructible, and its
specified completion map is invertible, naturally and independently of its resolution.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.5.9 and Remark 6.8.15
(blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof:
1. Apply integral-stratified-perfect-characterization on Y. Obtain finitely many
constructible locally closed strata and pro-etale covers with bounded finite-projective
R-complexes as local models. The detailed-category comparison retains the same completed
ring, reduction functors and uniform reduction bound.
2. Base change the strata along f and discard empty strata. They are locally closed,
constructible, disjoint and cover X. Base-changed trivializing families remain covering
by topos-functoriality-inverse-image.
3. The completed coefficient maps agree under composition after all finite projections.
Ringed-derived-monoidal-comparisons, the ordinary immersion restriction assertion of
immersion-completed-pullback-comparison, and ringed-derived-slice-localization therefore
compute ordinary pullback locally as B_V tensor_R L. Finite projective summands and their
bounded complexes compute derived pullback, so these are the required perfect models.
4. Apply integral-stratified-perfect-characterization on X: the output is in the detailed
integral category, with one uniform bound for its reductions, and is intrinsically complete.
5. For a good resolution Q, ordinary pullback F is K-flat with flat terms by
ringed-topos-kflat-pullback. The finite constant inverse-image map and exact finite
pullback identify F tensor D_n with f_n-star(Q tensor C_n). On tensors the map sends
(b tensor q) tensor a to 1 tensor (q tensor pi_n(b)a); the inverse inserts one. The
formulas commute with the actual quotient transitions and carry quotient units to the
augmentation used above. Use proetale-constant-exact and left-exact-site-inverse-image-tensor.
6. The valuation ring is a Noetherian DVR with finite quotients, by extension-integers-dvr
and valued-dvr-finite-quotients. The two-term complexes [R --t^n--> R] resolve the quotients.
Koszul-reconstruction makes the completion unit of the complete output invertible.
Exact products and integral-operations-well-defined compute that unit by the strict Roos
cone. The tower identification in step 5 carries both coordinates to the specified
chain map, hence gives invertibility of this very comparison.
7. On any chain map of good resolutions, both quotient-augmentation composites send
b tensor q to 1 tensor (v(q) tensor pi_n(b)). Their products and zero second coordinates
therefore commute strictly. Localizing proves naturality and independence under all
canonical resolution comparisons. No separatedness or base-field structure is used. -/
theorem ordinaryCompletedIntegralPullback
    [IsNoetherian X] [IsNoetherian Y]
    (_hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hYdim : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (_hXinv : IsUnit (l : Γ(X, ⊤))) (_hYinv : IsUnit (l : Γ(Y, ⊤)))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l E X ((ordinaryIntegralDerivedPull l E f).obj K) ∧
      IsIso ((ordinaryIntegralCompletionComparison l E f).app K) := by
  sorry

end WeilConjectures
