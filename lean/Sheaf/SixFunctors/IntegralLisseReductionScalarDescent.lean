/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.SixFunctors.IntegralLisseReductionConstruction
import Sheaf.SixFunctors.IntegralLisseCoefficientQuotients
import Mathlib.RingTheory.Ideal.Maps

/-!
# Descending a module action through coefficient reduction

Source: Bhatt--Scholze, Proposition 6.8.4(1), the finite coefficient reduction construction.
The action is constructed by lifting scalars, independently of the chosen lifts.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v r m
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules
namespace ScalarDescent

/-- Descend a module through a surjective ring homomorphism with trivial kernel action. -/
@[instance_reducible] def descendedModule {A B M : Type*} [Ring A] [Ring B]
    [AddCommGroup M] [Module A M] (f : A →+* B) (hf : Function.Surjective f)
    (hk : ∀ a : A, f a = 0 → ∀ x : M, a • x = 0) : Module B M := by
  let : SMul B M := ⟨fun b x ↦ Function.surjInv hf b • x⟩
  apply hf.moduleLeft f
  intro a x
  change Function.surjInv hf (f a) • x = a • x
  apply sub_eq_zero.mp
  rw [← sub_smul]
  apply hk
  rw [map_sub, Function.surjInv_eq hf, sub_self]

private theorem descendedModule_smul {A B M : Type*} [Ring A] [Ring B]
    [AddCommGroup M] [Module A M] (f : A →+* B) (hf : Function.Surjective f)
    (hk : ∀ a : A, f a = 0 → ∀ x : M, a • x = 0) (a : A) (x : M) :
    let _ := descendedModule f hf hk
    f a • x = a • x := by
  change Function.surjInv hf (f a) • x = a • x
  apply sub_eq_zero.mp
  rw [← sub_smul]
  apply hk
  rw [map_sub, Function.surjInv_eq hf, sub_self]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{r}} (q : R ⟶ S)
  (hs : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U).hom)
  (M : SheafOfModules.{m} R)
  (hk : ∀ (U : Cᵒᵖ) (a : R.obj.obj U), q.hom.app U a = 0 →
    ∀ x : M.val.obj U, a • x = 0)

/-- The scalar action on the unchanged section group, descended through a surjective map. -/
def sectionModule (U : Cᵒᵖ) : ModuleCat.{m} (S.obj.obj U) :=
  let _ := descendedModule (q.hom.app U).hom (hs U) (hk U)
  ModuleCat.of _ (M.val.obj U)

/-- Lifted scalars act by their original action. -/
theorem sectionModule_smul (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U) :
    (q.hom.app U a) • (show sectionModule q hs M hk U from x) =
      (show sectionModule q hs M hk U from a • x) :=
  descendedModule_smul (q.hom.app U).hom (hs U) (hk U) a x

/-- Descend the scalar action sectionwise; restriction maps keep their original functions. -/
def module : SheafOfModules.{m} S where
  val :=
    { obj := sectionModule q hs M hk
      map := fun {U V} f ↦ ModuleCat.ofHom
        (X := sectionModule q hs M hk U)
        (Y := (ModuleCat.restrictScalars (S.obj.map f).hom).obj (sectionModule q hs M hk V))
        { toFun := M.val.map f
          map_add' := map_add _
          map_smul' := fun s x ↦ by
            obtain ⟨a, rfl⟩ := hs U s
            change M.val.map f ((q.hom.app U a) •
                (show sectionModule q hs M hk U from x)) =
              (S.obj.map f (q.hom.app U a)) •
                (show sectionModule q hs M hk V from M.val.map f x)
            rw [sectionModule_smul, M.val.map_smul]
            rw [show S.obj.map f (q.hom.app U a) =
              q.hom.app V (R.obj.map f a) from
                ConcreteCategory.congr_hom (q.hom.naturality f).symm a]
            exact (sectionModule_smul q hs M hk V _ _).symm }
      map_id U := by
        ext x
        exact congrArg (fun f ↦ f x) (M.val.map_id U)
      map_comp f g := by
        ext x
        exact M.val.map_comp_apply f g x }
  isSheaf := M.isSheaf

/-- The restriction of the descended action is the original module, by the identity on sections. -/
def restrictionIso : (restrictScalars q).obj (module q hs M hk) ≅ M := by
  let h : (restrictScalars q).obj (module q hs M hk) ⟶ M :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
         (X := ((restrictScalars q).obj (module q hs M hk)).val.obj U)
         (Y := M.val.obj U)
         { toFun := id
           map_add' := fun _ _ ↦ rfl
           map_smul' := fun a x ↦ sectionModule_smul q hs M hk U a x }
       naturality := fun _ ↦ rfl }⟩
  let g : M ⟶ (restrictScalars q).obj (module q hs M hk) :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
         (X := M.val.obj U)
         (Y := ((restrictScalars q).obj (module q hs M hk)).val.obj U)
         { toFun := id
           map_add' := fun _ _ ↦ rfl
           map_smul' := fun a x ↦ (sectionModule_smul q hs M hk U a x).symm }
       naturality := fun _ ↦ rfl }⟩
  exact ⟨h, g, rfl, rfl⟩

/-- Scalar restriction along a sectionwise surjective map is fully faithful. -/
def fullyFaithful : (restrictScalars.{m} q).FullyFaithful where
  preimage {M N} f :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
         { toFun := f.val.app U
           map_add' := map_add _
           map_smul' := fun s x ↦ by
             obtain ⟨a, rfl⟩ := hs U s
             exact (f.val.app U).hom.map_smul a x }
       naturality := fun g ↦ by
         ext x
         exact congrArg (fun h ↦ h x) (f.val.naturality g) }⟩
  map_preimage f := by ext U x; rfl
  preimage_map f := by ext U x; rfl

end ScalarDescent
end SheafOfModules

namespace AlgebraicGeometry.ProEtale
open AlgebraicGeometry
universe t
variable (l : ℕ) [Fact l.Prime] (E : Type (t + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t})

/-- The actual coefficient reduction is surjective on each object. -/
theorem integralLisseReduction_surjective (n : ℕ) (U : X.ProEtᵒᵖ) :
    Function.Surjective ((integralLisseReduction l E X n).hom.app U).hom := by
  intro s
  obtain ⟨a, ha⟩ := (integralLisseCoefficient_sectionwise l E X n U).1 s
  refine ⟨a, ?_⟩
  change (integralLisseReduction l E X n).hom.app U a * 1 = s at ha
  simpa only [mul_one] using ha

/-- The kernel of coefficient reduction acts trivially on the scalar cokernel.
Source: Bhatt--Scholze, Proposition 6.8.4(1), construction of finite reductions
(blueprint: lem-sfb-integral-lisse-coefficient-kernel-action).
Proof: the uniformizer power annihilates the cokernel by scalar naturality and the
cokernel equation, after cancellation of the epic cokernel projection. Sectionwise
coefficient exactness writes each kernel section as that power times an integral
section. Associativity of the module action then makes its action vanish. -/
theorem integralLisseCoefficientKernel_annihilates
    (M : ringedSiteModules.{t + 1} (integralLisseRing l E X)) (n : ℕ)
    (U : X.ProEtᵒᵖ) (a : (integralLisseRing l E X).obj.obj U)
    (ha : (integralLisseReduction l E X n).hom.app U a = 0)
    (x : (integralLisseCokernel l E X M n).val.obj U) : a • x = 0 := by
  let b := Padic.coefficientExtensionUniformizer l E ^ (n + 1)
  let Q := integralLisseCokernel l E X M n
  have hz : integralLisseScalar l E X Q b = 0 := by
    apply (cancel_epi (cokernel.π (integralLisseScalar l E X M b))).1
    dsimp only [Q, integralLisseCokernel]
    rw [← integralLisseScalar_natural l E X (cokernel.π _) b,
      cokernel.condition, comp_zero]
  have hr : (integralLisseRingMap l E X
      ((sheafCompose _ (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (integralLisseReduction l E X n))).val.app U a = 0 := by
    change (integralLisseReduction l E X n).hom.app U a * 1 = 0
    rw [ha, zero_mul]
  obtain ⟨c, hc⟩ := (integralLisseCoefficient_sectionwise l E X n U).2 a |>.mp hr
  change (lisseIntegerSheafSized l E X).obj.obj U at c
  change lisseIntegerConstantSized l E X U b * c = a at hc
  rw [← hc, mul_smul]
  exact congrArg (fun f ↦ f.val.app U (c • x)) hz

/-- The actual scalar cokernel, with its action of the finite coefficient ring. -/
def integralLisseFiniteCokernel
    (M : ringedSiteModules.{t + 1} (integralLisseRing l E X)) (n : ℕ) :=
  SheafOfModules.ScalarDescent.module
    ((sheafCompose _ (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (integralLisseReduction l E X n))
    (integralLisseReduction_surjective l E X n) (integralLisseCokernel l E X M n)
    (integralLisseCoefficientKernel_annihilates l E X M n)

/-- Restriction of the finite scalar action recovers the actual cokernel. -/
def integralLisseFiniteCokernelIso
    (M : ringedSiteModules.{t + 1} (integralLisseRing l E X)) (n : ℕ) :
    (integralLisseFiniteRestriction l E X n).obj (integralLisseFiniteCokernel l E X M n) ≅
      integralLisseCokernel l E X M n :=
  SheafOfModules.ScalarDescent.restrictionIso _ _ _ _

end AlgebraicGeometry.ProEtale
