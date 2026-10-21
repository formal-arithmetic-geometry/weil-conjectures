/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSmallModelCompletedTensor
public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.Algebra.Homology.BifunctorLinear
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Linear
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Bilinearity of derived completed tensor and its raw rational Hom action

Source: blueprint, sec-six-functors/sk-rem-sf-pf-done/def-wf-tensor-product.md,
coefficient tensor model; Stacks Tags 06YS, 06YU, 099B, 0A0E, 00CX and 05G4
(blueprint: lem-sf-derived-completed-tensor-bilinearity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u v r w w₀ a
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace CategoryTheory
namespace DerivedCompletedTensor

attribute [local irreducible] KoszulSmallModel.complete
  SheafOfModules.siteDerivedTensorIndependentCoefficients

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The induced A-action is the existing global-section action restricted along s.
At U it sends f(x) to s(a)|U f(x), with the existing additive Hom groups.
Source: Stacks 03EK (blueprint: lem-sf-derived-completed-tensor-bilinearity). -/
@[instance_reducible]
def coefficientLinear (A : Type a) [CommRing A]
    (s : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r})) :
    Linear A (KoszulSmallModel.Modules R) :=
  letI : Linear (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r}))
      (KoszulSmallModel.Modules R) :=
    SheafOfModules.homLinear R.obj
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) s
    smul_comp := fun M N P z f g ↦ Linear.smul_comp M N P (s z) f g
    comp_smul := fun M N P f z g ↦ Linear.comp_smul M N P f (s z) g }

@[instance_reducible]
private def presheafLinear (A : Type a) [CommRing A]
    (s : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    Linear A (PresheafOfModules.{r} (R.obj ⋙ forget₂ CommRingCat RingCat)) where
  homModule M N := Module.compHom _ ((PresheafOfModules.sectionsSMulHom N).comp s)
  smul_comp := by
    intro M N P z f g
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact (g.app U).hom.map_smul _ _
  comp_smul := by intros; rfl

private theorem sheafTensorLinear (A : Type a) [CommRing A]
    (s : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    let := coefficientLinear R A s
    MonoidalLinear A (KoszulSmallModel.Modules R) := by
  let := coefficientLinear R A s
  change MonoidalLinear A (KoszulSmallModel.Modules R)
  let O := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let : Linear A (PresheafOfModules.{r} O.obj) := presheafLinear R A s
  have : (SheafOfModules.forget.{r} O).Linear A := ⟨fun _ _ ↦ rfl⟩
  have : (PresheafOfModules.restrictScalars.{r} (𝟙 O.obj)).Linear A :=
    ⟨fun _ _ ↦ rfl⟩
  have : (PresheafOfModules.sheafification.{r} (𝟙 O.obj)).Linear A :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).left_adjoint_linear
  have hp (M : PresheafOfModules.{r} O.obj) :
      (MonoidalCategory.tensorRight M).Linear A := by
    constructor
    intro N N' f z
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    let c : R.obj.obj U := (s z).val U
    change ((c • (f.app U).hom x) ⊗ₜ[R.obj.obj U] y) =
      c • ((f.app U).hom x ⊗ₜ[R.obj.obj U] y)
    exact TensorProduct.smul_tmul' _ _ _
  have hr (M : KoszulSmallModel.Modules R) :
      (MonoidalCategory.tensorRight M).Linear A := by
    have : (SheafOfModules.forget O ⋙ MonoidalCategory.tensorRight M.val ⋙
        PresheafOfModules.sheafification.{r} (𝟙 O.obj)).Linear A := inferInstance
    exact Functor.linear_of_iso _ (SheafOfModules.tensorRightPresentation R M).symm
  have hl (M : KoszulSmallModel.Modules R) :
      (MonoidalCategory.tensorLeft M).Linear A :=
    Functor.linear_of_iso _ (BraidedCategory.tensorLeftIsoTensorRight M).symm
  exact ⟨fun X _ _ z f ↦ (MonoidalCategory.tensorLeft X).map_smul z f,
    fun z _ _ f X ↦ (MonoidalCategory.tensorRight X).map_smul z f⟩

private theorem reflectorLinear {D : Type*} [Category* D] [Preadditive D]
    (A : Type*) [CommRing A] [Linear A D] (P : ObjectProperty D)
    (L : D ⥤ P.FullSubcategory) (η : 𝟭 D ⟶ L ⋙ P.ι)
    (hL : ∀ M N, Function.Injective (fun f : L.obj M ⟶ N ↦ η.app M ≫ f.hom)) :
    L.Additive ∧ L.Linear A := by
  constructor
  · constructor
    intro M N f g
    apply hL M (L.obj N)
    change η.app M ≫ (L.map (f + g)).hom =
      η.app M ≫ ((L.map f).hom + (L.map g).hom)
    have hn (f : M ⟶ N) : f ≫ η.app N = η.app M ≫ (L.map f).hom :=
      η.naturality f
    rw [← hn, Preadditive.comp_add, ← hn, ← hn, Preadditive.add_comp]
  · constructor
    intro M N f z
    apply hL M (L.obj N)
    change η.app M ≫ (L.map (z • f)).hom = η.app M ≫ (z • (L.map f).hom)
    have hn (f : M ⟶ N) : f ≫ η.app N = η.app M ≫ (L.map f).hom :=
      η.naturality f
    rw [← hn, Linear.comp_smul, ← hn, Linear.smul_comp]

section ScalarExtension
variable {D : Type*} [Category* D] [Preadditive D]
  (A : Type*) [CommRing A] [Linear A D] (B : D × D ⥤ D)
  [∀ M, ((Functor.curry.obj B).obj M).Additive]
  [∀ M, ((Functor.curry.obj B).obj M).Linear A]
  [∀ M, ((Functor.curry.obj B).flip.obj M).Additive]
  [∀ M, ((Functor.curry.obj B).flip.obj M).Linear A]

private def integralAction (M M' N N' : D) :
    (M ⟶ M') →ₗ[A] (N ⟶ N') →ₗ[A] (B.obj (M, N) ⟶ B.obj (M', N')) where
  toFun f :=
    { toFun := fun g ↦ B.map (f, g)
      map_add' := by
        intro g h
        have e (g : N ⟶ N') : B.map (f, g) =
            B.map (X := (M, N)) (Y := (M', N)) (f, 𝟙 N) ≫
          B.map (X := (M', N)) (Y := (M', N')) (𝟙 M', g) := by
          simpa using (B.map_comp (X := (M, N)) (Y := (M', N)) (Z := (M', N'))
            (f, 𝟙 N) (𝟙 M', g))
        rw [e, e g, e h]
        change B.map (X := (M, N)) (Y := (M', N)) (f, 𝟙 N) ≫
          ((Functor.curry.obj B).obj M').map (g + h) = _
        rw [Functor.map_add, Preadditive.comp_add]
        rfl
      map_smul' := by
        intro z g
        have e (g : N ⟶ N') : B.map (f, g) =
            B.map (X := (M, N)) (Y := (M', N)) (f, 𝟙 N) ≫
          B.map (X := (M', N)) (Y := (M', N')) (𝟙 M', g) := by
          simpa using (B.map_comp (X := (M, N)) (Y := (M', N)) (Z := (M', N'))
            (f, 𝟙 N) (𝟙 M', g))
        rw [e, e g]
        change B.map (X := (M, N)) (Y := (M', N)) (f, 𝟙 N) ≫
          ((Functor.curry.obj B).obj M').map (z • g) = _
        rw [Functor.map_smul, Linear.comp_smul]
        rfl }
  map_add' := by
    intro f h
    ext g
    have e (f : M ⟶ M') : B.map (f, g) =
        B.map (X := (M, N)) (Y := (M', N)) (f, 𝟙 N) ≫
          B.map (X := (M', N)) (Y := (M', N')) (𝟙 M', g) := by
          simpa using (B.map_comp (X := (M, N)) (Y := (M', N)) (Z := (M', N'))
            (f, 𝟙 N) (𝟙 M', g))
    change B.map (Prod.mkHom (f + h) g) =
      B.map (Prod.mkHom f g) + B.map (Prod.mkHom h g)
    rw [e, e f, e h]
    change ((Functor.curry.obj B).flip.obj N).map (f + h) ≫
      B.map (X := (M', N)) (Y := (M', N')) (𝟙 M', g) = _
    rw [Functor.map_add, Preadditive.add_comp]
    rfl
  map_smul' := by
    intro z f
    ext g
    have e (f : M ⟶ M') : B.map (f, g) =
        B.map (X := (M, N)) (Y := (M', N)) (f, 𝟙 N) ≫
          B.map (X := (M', N)) (Y := (M', N')) (𝟙 M', g) := by
          simpa using (B.map_comp (X := (M, N)) (Y := (M', N)) (Z := (M', N'))
            (f, 𝟙 N) (𝟙 M', g))
    change B.map (Prod.mkHom (z • f) g) = z • B.map (Prod.mkHom f g)
    rw [e, e f]
    change ((Functor.curry.obj B).flip.obj N).map (z • f) ≫
      B.map (X := (M', N)) (Y := (M', N')) (𝟙 M', g) = _
    rw [Functor.map_smul, Linear.smul_comp]
    rfl

private def localizedAction (p : A) (M M' N N' : D) :
    (Localization.Away p ⊗[A] (M ⟶ M')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[A] (N ⟶ N')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[A] (B.obj (M, N) ⟶ B.obj (M', N'))) :=
  TensorProduct.curry
    (((TensorProduct.lift (integralAction A B M M' N N')).baseChange (Localization.Away p)).comp
      (AlgebraTensorModule.distribBaseChange A (Localization.Away p)
        (M ⟶ M') (N ⟶ N')).symm.toLinearMap)

private theorem localizedAction_tmul (p : A) (M M' N N' : D)
    (f : M ⟶ M') (g : N ⟶ N') (x y : Localization.Away p) :
    localizedAction A B p M M' N N' (x ⊗ₜ[A] f) (y ⊗ₜ[A] g) =
      (x * y) ⊗ₜ[A] B.map (f, g) := by
  simp [localizedAction, integralAction]

private theorem localizedAction_comp (p : A) (M M' M'' N N' N'' : D)
    (f : Localization.Away p ⊗[A] (M ⟶ M'))
    (f' : Localization.Away p ⊗[A] (M' ⟶ M''))
    (g : Localization.Away p ⊗[A] (N ⟶ N'))
    (g' : Localization.Away p ⊗[A] (N' ⟶ N'')) :
    localizedAction A B p M M'' N N''
        (ScalarLocalization.composition A D p M M' M'' f' f)
        (ScalarLocalization.composition A D p N N' N'' g' g) =
      ScalarLocalization.composition A D p
        (B.obj (M, N)) (B.obj (M', N')) (B.obj (M'', N''))
        (localizedAction A B p M' M'' N' N'' f' g')
        (localizedAction A B p M M' N N' f g) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | add f h hf hh => simp only [map_add, LinearMap.add_apply, hf, hh]
  | tmul x f =>
    induction f' using TensorProduct.induction_on with
    | zero => simp
    | add f' h hf hh => simp only [map_add, LinearMap.add_apply, hf, hh]
    | tmul x' f' =>
      induction g using TensorProduct.induction_on with
      | zero => simp
      | add g h hg hh => simp only [map_add, hg, hh]
      | tmul y g =>
        induction g' using TensorProduct.induction_on with
        | zero => simp
        | add g' h hg hh => simp only [map_add, LinearMap.add_apply, hg, hh]
        | tmul y' g' =>
          simp only [ScalarLocalization.composition_tmul, localizedAction_tmul]
          have he : B.map (X := (M, N)) (Y := (M'', N'')) (f ≫ f', g ≫ g') =
              B.map (X := (M, N)) (Y := (M', N')) (f, g) ≫
                B.map (X := (M', N')) (Y := (M'', N'')) (f', g') := by
            simpa using B.map_comp (X := (M, N)) (Y := (M', N')) (Z := (M'', N''))
              (f, g) (f', g')
          rw [he]
          congr 1
          ring

private def localizedBifunctor (p : A) :
    ScalarLocalization A D p × ScalarLocalization A D p ⥤ ScalarLocalization A D p where
  obj X := ⟨B.obj (X.1.obj, X.2.obj)⟩
  map {X Y} f := localizedAction A B p X.1.obj Y.1.obj X.2.obj Y.2.obj f.1 f.2
  map_id X := by
    change localizedAction A B p _ _ _ _ (1 ⊗ₜ[A] 𝟙 _) (1 ⊗ₜ[A] 𝟙 _) = _
    rw [localizedAction_tmul, one_mul]
    congr 1
    exact B.map_id _
  map_comp {X Y Z} f g := localizedAction_comp A B p _ _ _ _ _ _ f.1 g.1 f.2 g.2

private theorem restrictBilinear
    (P : ObjectProperty D) (L : D ⥤ P.FullSubcategory) [L.Additive] [L.Linear A]
    (T : D × D ⥤ D)
    [∀ M, ((Functor.curry.obj T).obj M).Additive]
    [∀ M, ((Functor.curry.obj T).obj M).Linear A]
    [∀ M, ((Functor.curry.obj T).flip.obj M).Additive]
    [∀ M, ((Functor.curry.obj T).flip.obj M).Linear A] :
    ∀ M : P.FullSubcategory,
      ((Functor.curry.obj (P.ι.prod P.ι ⋙ T ⋙ L)).obj M).Additive ∧
      ((Functor.curry.obj (P.ι.prod P.ι ⋙ T ⋙ L)).obj M).Linear A ∧
      ((Functor.curry.obj (P.ι.prod P.ι ⋙ T ⋙ L)).flip.obj M).Additive ∧
      ((Functor.curry.obj (P.ι.prod P.ι ⋙ T ⋙ L)).flip.obj M).Linear A := by
  intro M
  have eL : (Functor.curry.obj (P.ι.prod P.ι ⋙ T ⋙ L)).obj M ≅
      P.ι ⋙ (Functor.curry.obj T).obj M.obj ⋙ L := Iso.refl _
  have eR : (Functor.curry.obj (P.ι.prod P.ι ⋙ T ⋙ L)).flip.obj M ≅
      P.ι ⋙ (Functor.curry.obj T).flip.obj M.obj ⋙ L := Iso.refl _
  exact ⟨Functor.additive_of_iso eL.symm, Functor.linear_of_iso A eL.symm,
    Functor.additive_of_iso eR.symm, Functor.linear_of_iso A eR.symm⟩

private theorem scalarExtension :
      ∀ p : A, ∃ β : ∀ M M' N N' : D,
          ((Localization.Away p ⊗[A] (M ⟶ M')) →ₗ[Localization.Away p]
            (Localization.Away p ⊗[A] (N ⟶ N')) →ₗ[Localization.Away p]
              (Localization.Away p ⊗[A] (B.obj (M, N) ⟶ B.obj (M', N')))),
        (∀ (M M' N N' : D)
          (f : M ⟶ M') (g : N ⟶ N') (x y : Localization.Away p),
          β M M' N N' (x ⊗ₜ[A] f) (y ⊗ₜ[A] g) =
            (x * y) ⊗ₜ[A] B.map (f, g)) ∧
        (∀ (M M' N N' : D)
          (β' : ((Localization.Away p ⊗[A] (M ⟶ M')) →ₗ[Localization.Away p]
            (Localization.Away p ⊗[A] (N ⟶ N')) →ₗ[Localization.Away p]
              (Localization.Away p ⊗[A] (B.obj (M, N) ⟶ B.obj (M', N'))))),
          (∀ (f : M ⟶ M') (g : N ⟶ N') (x y : Localization.Away p),
            β' (x ⊗ₜ[A] f) (y ⊗ₜ[A] g) =
              (x * y) ⊗ₜ[A] B.map (f, g)) → β' = β M M' N N') ∧
        (∀ M N : D,
          β M M N N (1 ⊗ₜ[A] 𝟙 M) (1 ⊗ₜ[A] 𝟙 N) =
            (1 : Localization.Away p) ⊗ₜ[A] 𝟙 (B.obj (M, N))) ∧
        (∀ (M M' M'' N N' N'' : D)
          (f : Localization.Away p ⊗[A] (M ⟶ M'))
          (f' : Localization.Away p ⊗[A] (M' ⟶ M''))
          (g : Localization.Away p ⊗[A] (N ⟶ N'))
          (g' : Localization.Away p ⊗[A] (N' ⟶ N'')),
          β M M'' N N''
              (ScalarLocalization.composition A _ p M M' M'' f' f)
              (ScalarLocalization.composition A _ p N N' N'' g' g) =
            ScalarLocalization.composition A _ p
              (B.obj (M, N)) (B.obj (M', N'))
              (B.obj (M'', N''))
              (β M' M'' N' N'' f' g') (β M M' N N' f g)) ∧
        (∀ (M M' N N' : D)
          (f : M ⟶ M') (g : N ⟶ N') (k t : ℕ),
          β M M' N N'
              (((IsLocalization.Away.invSelf p : Localization.Away p) ^ k) ⊗ₜ[A] f)
              (((IsLocalization.Away.invSelf p : Localization.Away p) ^ t) ⊗ₜ[A] g) =
            ((IsLocalization.Away.invSelf p : Localization.Away p) ^ (k + t)) ⊗ₜ[A]
              B.map (f, g)) ∧
        ∃ F : ScalarLocalization A D p ×
              ScalarLocalization A D p ⥤
              ScalarLocalization A D p,
          (∀ M N : D,
            F.obj (⟨M⟩, ⟨N⟩) = ⟨B.obj (M, N)⟩) ∧
          (∀ (M M' N N' : D)
            (f : Localization.Away p ⊗[A] (M ⟶ M'))
            (g : Localization.Away p ⊗[A] (N ⟶ N')),
            HEq (F.map (X := (⟨M⟩, ⟨N⟩)) (Y := (⟨M'⟩, ⟨N'⟩)) (f, g))
              (β M M' N N' f g)) := by
  intro p
  refine ⟨localizedAction A B p, localizedAction_tmul A B p, ?_, ?_,
    localizedAction_comp A B p, ?_, localizedBifunctor A B p, ?_, ?_⟩
  · intro M M' N N' β' hβ
    ext f g
    exact (hβ f g 1 1).trans (localizedAction_tmul A B p M M' N N' f g 1 1).symm
  · intro M N
    rw [localizedAction_tmul, one_mul]
    congr 1
    exact B.map_id (M, N)
  · intro M M' N N' f g k t
    rw [localizedAction_tmul, pow_add]
  · intro M N
    rfl
  · intro M M' N N' f g
    rfl

private theorem completedArgument (P : ObjectProperty D)
    (T : D × D ⥤ D) (L : D ⥤ P.FullSubcategory)
    (η : 𝟭 D ⟶ L ⋙ P.ι)
    (hL : ∀ M N, Function.Injective (fun f : L.obj M ⟶ N ↦ η.app M ≫ f.hom))
    (hT : ∀ M : D,
      ((Functor.curry.obj T).obj M).Additive ∧
      ((Functor.curry.obj T).obj M).Linear A ∧
      ((Functor.curry.obj T).flip.obj M).Additive ∧
      ((Functor.curry.obj T).flip.obj M).Linear A) :
      L.Additive ∧ L.Linear A ∧
      (∀ M : D,
        ((Functor.curry.obj T).obj
          M).Additive ∧
        ((Functor.curry.obj T).obj
          M).Linear A ∧
        ((Functor.curry.obj T).flip.obj
          M).Additive ∧
        ((Functor.curry.obj T).flip.obj
          M).Linear A) ∧
      (∀ M : P.FullSubcategory,
        ((Functor.curry.obj (P.ι.prod P.ι ⋙ T ⋙ L)).obj M).Additive ∧
        ((Functor.curry.obj (P.ι.prod P.ι ⋙ T ⋙ L)).obj M).Linear A ∧
        ((Functor.curry.obj (P.ι.prod P.ι ⋙ T ⋙ L)).flip.obj M).Additive ∧
        ((Functor.curry.obj (P.ι.prod P.ι ⋙ T ⋙ L)).flip.obj M).Linear A) ∧
      ∀ p : A, ∃ β : ∀ M M' N N' : P.FullSubcategory,
          ((Localization.Away p ⊗[A] (M ⟶ M')) →ₗ[Localization.Away p]
            (Localization.Away p ⊗[A] (N ⟶ N')) →ₗ[Localization.Away p]
              (Localization.Away p ⊗[A]
                ((P.ι.prod P.ι ⋙ T ⋙ L).obj (M, N) ⟶
                  (P.ι.prod P.ι ⋙ T ⋙ L).obj (M', N')))),
        (∀ (M M' N N' : P.FullSubcategory)
          (f : M ⟶ M') (g : N ⟶ N') (x y : Localization.Away p),
          β M M' N N' (x ⊗ₜ[A] f) (y ⊗ₜ[A] g) =
            (x * y) ⊗ₜ[A] (P.ι.prod P.ι ⋙ T ⋙ L).map (f, g)) ∧
        (∀ (M M' N N' : P.FullSubcategory)
          (β' : ((Localization.Away p ⊗[A] (M ⟶ M')) →ₗ[Localization.Away p]
            (Localization.Away p ⊗[A] (N ⟶ N')) →ₗ[Localization.Away p]
              (Localization.Away p ⊗[A]
                ((P.ι.prod P.ι ⋙ T ⋙ L).obj (M, N) ⟶
                  (P.ι.prod P.ι ⋙ T ⋙ L).obj (M', N'))))),
          (∀ (f : M ⟶ M') (g : N ⟶ N') (x y : Localization.Away p),
            β' (x ⊗ₜ[A] f) (y ⊗ₜ[A] g) =
              (x * y) ⊗ₜ[A] (P.ι.prod P.ι ⋙ T ⋙ L).map (f, g)) → β' = β M M' N N') ∧
        (∀ M N : P.FullSubcategory,
          β M M N N (1 ⊗ₜ[A] 𝟙 M) (1 ⊗ₜ[A] 𝟙 N) =
            (1 : Localization.Away p) ⊗ₜ[A] 𝟙 ((P.ι.prod P.ι ⋙ T ⋙ L).obj (M, N))) ∧
        (∀ (M M' M'' N N' N'' : P.FullSubcategory)
          (f : Localization.Away p ⊗[A] (M ⟶ M'))
          (f' : Localization.Away p ⊗[A] (M' ⟶ M''))
          (g : Localization.Away p ⊗[A] (N ⟶ N'))
          (g' : Localization.Away p ⊗[A] (N' ⟶ N'')),
          β M M'' N N''
              (ScalarLocalization.composition A _ p M M' M'' f' f)
              (ScalarLocalization.composition A _ p N N' N'' g' g) =
            ScalarLocalization.composition A _ p
              ((P.ι.prod P.ι ⋙ T ⋙ L).obj (M, N)) ((P.ι.prod P.ι ⋙ T ⋙ L).obj (M', N'))
              ((P.ι.prod P.ι ⋙ T ⋙ L).obj (M'', N''))
              (β M' M'' N' N'' f' g') (β M M' N N' f g)) ∧
        (∀ (M M' N N' : P.FullSubcategory)
          (f : M ⟶ M') (g : N ⟶ N') (k t : ℕ),
          β M M' N N'
              (((IsLocalization.Away.invSelf p : Localization.Away p) ^ k) ⊗ₜ[A] f)
              (((IsLocalization.Away.invSelf p : Localization.Away p) ^ t) ⊗ₜ[A] g) =
            ((IsLocalization.Away.invSelf p : Localization.Away p) ^ (k + t)) ⊗ₜ[A]
              (P.ι.prod P.ι ⋙ T ⋙ L).map (f, g)) ∧
        ∃ F : ScalarLocalization A P.FullSubcategory p ×
              ScalarLocalization A P.FullSubcategory p ⥤
              ScalarLocalization A P.FullSubcategory p,
          (∀ M N : P.FullSubcategory,
            F.obj (⟨M⟩, ⟨N⟩) = ⟨(P.ι.prod P.ι ⋙ T ⋙ L).obj (M, N)⟩) ∧
          (∀ (M M' N N' : P.FullSubcategory)
            (f : Localization.Away p ⊗[A] (M ⟶ M'))
            (g : Localization.Away p ⊗[A] (N ⟶ N')),
            HEq (F.map (X := (⟨M⟩, ⟨N⟩)) (Y := (⟨M'⟩, ⟨N'⟩)) (f, g))
              (β M M' N N' f g)) := by
  obtain ⟨hLa, hLl⟩ := reflectorLinear A P L η hL
  have := hLa
  have := hLl
  have (M : D) := (hT M).1
  have (M : D) := (hT M).2.1
  have (M : D) := (hT M).2.2.1
  have (M : D) := (hT M).2.2.2
  let B := P.ι.prod P.ι ⋙ T ⋙ L
  have hB := restrictBilinear A P L T
  have (M : P.FullSubcategory) := (hB M).1
  have (M : P.FullSubcategory) := (hB M).2.1
  have (M : P.FullSubcategory) := (hB M).2.2.1
  have (M : P.FullSubcategory) := (hB M).2.2.2
  exact ⟨hLa, hLl, hT, hB, scalarExtension A B⟩

end ScalarExtension

variable [HasDerivedCategory.{w} (KoszulSmallModel.Modules R)]

private theorem derivedTensorLinear (A : Type a) [CommRing A]
    (s : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    let := coefficientLinear R A s
    ∀ M : DerivedCategory (KoszulSmallModel.Modules R),
      ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).obj
        M).Additive ∧
      ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).obj
        M).Linear A ∧
      ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).flip.obj
        M).Additive ∧
      ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).flip.obj
        M).Linear A := by
  classical
  let := coefficientLinear R A s
  change ∀ M : DerivedCategory (KoszulSmallModel.Modules R), _
  have : MonoidalLinear A (KoszulSmallModel.Modules R) := sheafTensorLinear R A s
  let T := SheafOfModules.KFlatFixedTensor.derivedTensor R
  obtain ⟨sh, hs⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  let := sh
  intro M
  let G := DerivedCategory.Q.objPreimage M
  obtain ⟨K, f, hK, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
  have := hf
  have hKf : ∀ n, SheafOfModules.IsFlatOnSite (J := J) (R := R) (K.X n) :=
    fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (K.X n)).symm (hflat n)
  let e : DerivedCategory.Q.obj K ≅ M :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  have h := hs K hK hKf
  have : (T.obj (DerivedCategory.Q.obj K)).IsTriangulated := h.2.2.1.1
  have : (T.flip.obj (DerivedCategory.Q.obj K)).IsTriangulated := h.2.2.1.2
  have : (T.obj (DerivedCategory.Q.obj K)).Additive := inferInstance
  have : (T.flip.obj (DerivedCategory.Q.obj K)).Additive := inferInstance
  obtain ⟨cL, _⟩ := h.2.2.2.1
  obtain ⟨cR, _⟩ := h.2.2.2.2.1
  have : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (KoszulSmallModel.Modules R) (.up ℤ))
      ((SheafOfModules.KFlatFixedTensor.totalTensor R).obj K ⋙ DerivedCategory.Q)
      (T.obj (DerivedCategory.Q.obj K)) := ⟨cL.symm⟩
  have : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (KoszulSmallModel.Modules R) (.up ℤ))
      ((SheafOfModules.KFlatFixedTensor.totalTensor R).flip.obj K ⋙ DerivedCategory.Q)
      (T.flip.obj (DerivedCategory.Q.obj K)) := ⟨cR.symm⟩
  have : (T.obj (DerivedCategory.Q.obj K)).Linear A :=
    (Localization.functor_linear_iff DerivedCategory.Q
      (HomologicalComplex.quasiIso (KoszulSmallModel.Modules R) (.up ℤ)) A
      ((SheafOfModules.KFlatFixedTensor.totalTensor R).obj K ⋙ DerivedCategory.Q)
      (T.obj (DerivedCategory.Q.obj K))).1 inferInstance
  have : (T.flip.obj (DerivedCategory.Q.obj K)).Linear A :=
    (Localization.functor_linear_iff DerivedCategory.Q
      (HomologicalComplex.quasiIso (KoszulSmallModel.Modules R) (.up ℤ)) A
      ((SheafOfModules.KFlatFixedTensor.totalTensor R).flip.obj K ⋙ DerivedCategory.Q)
      (T.flip.obj (DerivedCategory.Q.obj K))).1 inferInstance
  let eL := T.mapIso e
  let eR := T.flip.mapIso e
  exact ⟨Functor.additive_of_iso eL, Functor.linear_of_iso A eL,
    Functor.additive_of_iso eR, Functor.linear_of_iso A eR⟩

variable [HasDerivedCategory.{w₀} (ringedSiteModules.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))]
  [∀ U : SmallModel.{r} C, HasDerivedCategory.{w₀} (SheafOfModules.{r}
    ((sheafCompose (((equivSmallModel.{r} C).inverse.inducedTopology J).over U)
      (forget₂ CommRingCat.{r} RingCat.{r})).obj ((KoszulSmallModel.ring R).over U)))]

variable (I : ringedSiteModules.{r}
  ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))
  (ι : I ⟶ SheafOfModules.unit.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))

/-- Bilinear maps on the two raw localized Hom modules. This is only an abbreviation
for ordinary curried linear maps, using the dependency's scalar-first tensor convention.
Source: blueprint def-wf-tensor-product
(blueprint: lem-sf-derived-completed-tensor-bilinearity). -/
abbrev HomAction (A : Type a) [CommRing A]
    [Linear A (KoszulSmallModel.Modules R)]
    (L : DerivedCategory (KoszulSmallModel.Modules R) ⥤
      (KoszulSmallModel.complete R I ι).FullSubcategory) (p : A)
    (M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory) :=
  (Localization.Away p ⊗[A] (M ⟶ M')) →ₗ[Localization.Away p]
    (Localization.Away p ⊗[A] (N ⟶ N')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[A] ((tensor R I ι L).obj (M, N) ⟶
        (tensor R I ι L).obj (M', N')))


/-- All seven clauses of the node, with the specified tensor and a natural universal
Koszul unit. The ideal mono and hgen specify exactly the finite generated ideal;
L, eta and hL say that L is its reflector, as stipulated in the node.

Source: blueprint def-wf-tensor-product, coefficient tensor model;
Stacks 03EK, 05RU, 06YS, 06YU, 099B, 0A0E, 00CX and 05G4
(blueprint: lem-sf-derived-completed-tensor-bilinearity).

Proof plan:
1. On module Hom groups use (a f)_U(x)=s(a)|U f_U(x). Composition is bilinear.
Sheaf tensor is separately linear by tensor balancing before sheafification; equality
passes to sheafification. On each signed total summand the map is f^i tensor g^j,
so sums and scalars commute with totalization.
2. The localization Q is additive (lem-sfb-derived-localization-additive).
lem-sfb-additive-localization-linear gives the induced A-action and linearity of Q.
3. For fixed flat-term K-flat P, lem-weil-pbc-kflat-fixed-tensor-triangulated gives
additive descended tensor functors. Their comparisons identify their composites with Q
with the linear total tensors of steps 1-2. Apply lem-sfb-linear-localization-descent.
Essential surjectivity of Q and lem-pc-kflat-resolution represent every derived
object by such P. Conjugation by its representative isomorphism preserves linearity.
4. Naturality of eta identifies eta_X followed by L(af+bg) with both eta_X followed
by a L(f)+b L(g). Injectivity of hL, with complete target LY, proves the equality.
This proves additivity and linearity of the specified reflector without linear choices.
5. Restrict tensor to the complete full subcategory and compose with L. Fixed-variable
functors are additive and linear, and simultaneous action is bilinear by composition.
6. Apply def-weil-module-base-change to the integral bilinear Hom map and A -> A[1/p].
The unique bilinear extension sends (x tensor f,y tensor g) to xy tensor B(f,g),
with the dependency's scalar-first convention. No flatness or torsion assumption enters.
7. The composition formula of lem-weil-linear-scalar-localization-category and
functoriality of B prove identity and composition on pure tensors. Each tensor is a
finite sum of pure tensors; multilinearity proves the laws on all arrows. These laws
give the bifunctor F with the prescribed object map and Hom action. Substitute inverse
powers of p in step 6 to obtain the denominator formula, including A[1/p]=0. -/
theorem bilinearity (A : Type a) [CommRing A]
    (s : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r}))
    (n : ℕ) (b : Fin n → (R.obj ⋙ forget CommRingCat.{r}).sections) [Mono ι]
    (_hgen : ∀ U : SmallModel.{r} C,
      IsRingedIdealGeneratingList (KoszulSmallModel.ring R) I ι U n
        (fun i ↦ (KoszulSmallModel.globalSection R (b i)).val (op U)))
    (L : DerivedCategory (KoszulSmallModel.Modules R) ⥤
      (KoszulSmallModel.complete R I ι).FullSubcategory)
    (η : 𝟭 (DerivedCategory (KoszulSmallModel.Modules R)) ⟶
      L ⋙ (KoszulSmallModel.complete R I ι).ι)
    (_hL : ∀ (M : DerivedCategory (KoszulSmallModel.Modules R))
      (N : (KoszulSmallModel.complete R I ι).FullSubcategory),
      Function.Bijective (fun f : L.obj M ⟶ N ↦ η.app M ≫ f.hom)) :
    (fun [_scalar : Linear A (KoszulSmallModel.Modules R)] ↦
      L.Additive ∧ L.Linear A ∧
      (∀ M : DerivedCategory (KoszulSmallModel.Modules R),
        ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).obj
          M).Additive ∧
        ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).obj
          M).Linear A ∧
        ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).flip.obj
          M).Additive ∧
        ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).flip.obj
          M).Linear A) ∧
      (∀ M : (KoszulSmallModel.complete R I ι).FullSubcategory,
        ((Functor.curry.obj (tensor R I ι L)).obj M).Additive ∧
        ((Functor.curry.obj (tensor R I ι L)).obj M).Linear A ∧
        ((Functor.curry.obj (tensor R I ι L)).flip.obj M).Additive ∧
        ((Functor.curry.obj (tensor R I ι L)).flip.obj M).Linear A) ∧
      ∀ p : A, ∃ β : ∀ M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory,
          HomAction R I ι A L p M M' N N',
        (∀ (M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory)
          (f : M ⟶ M') (g : N ⟶ N') (x y : Localization.Away p),
          β M M' N N' (x ⊗ₜ[A] f) (y ⊗ₜ[A] g) =
            (x * y) ⊗ₜ[A] (tensor R I ι L).map (f, g)) ∧
        (∀ (M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory)
          (β' : HomAction R I ι A L p M M' N N'),
          (∀ (f : M ⟶ M') (g : N ⟶ N') (x y : Localization.Away p),
            β' (x ⊗ₜ[A] f) (y ⊗ₜ[A] g) =
              (x * y) ⊗ₜ[A] (tensor R I ι L).map (f, g)) → β' = β M M' N N') ∧
        (∀ M N : (KoszulSmallModel.complete R I ι).FullSubcategory,
          β M M N N (1 ⊗ₜ[A] 𝟙 M) (1 ⊗ₜ[A] 𝟙 N) =
            (1 : Localization.Away p) ⊗ₜ[A] 𝟙 ((tensor R I ι L).obj (M, N))) ∧
        (∀ (M M' M'' N N' N'' : (KoszulSmallModel.complete R I ι).FullSubcategory)
          (f : Localization.Away p ⊗[A] (M ⟶ M'))
          (f' : Localization.Away p ⊗[A] (M' ⟶ M''))
          (g : Localization.Away p ⊗[A] (N ⟶ N'))
          (g' : Localization.Away p ⊗[A] (N' ⟶ N'')),
          β M M'' N N''
              (ScalarLocalization.composition A _ p M M' M'' f' f)
              (ScalarLocalization.composition A _ p N N' N'' g' g) =
            ScalarLocalization.composition A _ p
              ((tensor R I ι L).obj (M, N)) ((tensor R I ι L).obj (M', N'))
              ((tensor R I ι L).obj (M'', N''))
              (β M' M'' N' N'' f' g') (β M M' N N' f g)) ∧
        (∀ (M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory)
          (f : M ⟶ M') (g : N ⟶ N') (k t : ℕ),
          β M M' N N'
              (((IsLocalization.Away.invSelf p : Localization.Away p) ^ k) ⊗ₜ[A] f)
              (((IsLocalization.Away.invSelf p : Localization.Away p) ^ t) ⊗ₜ[A] g) =
            ((IsLocalization.Away.invSelf p : Localization.Away p) ^ (k + t)) ⊗ₜ[A]
              (tensor R I ι L).map (f, g)) ∧
        ∃ F : ScalarLocalization A (KoszulSmallModel.complete R I ι).FullSubcategory p ×
              ScalarLocalization A (KoszulSmallModel.complete R I ι).FullSubcategory p ⥤
              ScalarLocalization A (KoszulSmallModel.complete R I ι).FullSubcategory p,
          (∀ M N : (KoszulSmallModel.complete R I ι).FullSubcategory,
            F.obj (⟨M⟩, ⟨N⟩) = ⟨(tensor R I ι L).obj (M, N)⟩) ∧
          (∀ (M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory)
            (f : Localization.Away p ⊗[A] (M ⟶ M'))
            (g : Localization.Away p ⊗[A] (N ⟶ N')),
            HEq (F.map (X := (⟨M⟩, ⟨N⟩)) (Y := (⟨M'⟩, ⟨N'⟩)) (f, g))
              (β M M' N N' f g))) (_scalar := coefficientLinear R A s) := by
  let := coefficientLinear R A s
  exact completedArgument A (KoszulSmallModel.complete R I ι)
    (SheafOfModules.siteDerivedTensorIndependentCoefficients J R) L η
    (fun M N ↦ (_hL M N).1) (derivedTensorLinear R A s)

end DerivedCompletedTensor
end CategoryTheory
