/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linearity of localized extension by zero on derived module sheaves

Source: Stacks Project, Modules on Sites, Tags 03CY, 03DI and 03DJ
(blueprint: lem-cbc-localized-extension-zero-linear-derived).
-/

@[expose] public section
set_option autoImplicit false
universe u a w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private abbrev underlyingRing {D : Type (u + 1)} [Category.{u} D]
    {K : GrothendieckTopology D} (S : Sheaf K CommRingCat.{u + 1}) :=
  (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S

private def sectionScalar {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    (S : Sheaf K CommRingCat.{u + 1}) (B : Type a) [CommRing B]
    (sigma : ∀ V : Dᵒᵖ, B →+* S.obj.obj V)
    (hsigma : ∀ {V W : Dᵒᵖ} (f : V ⟶ W) (b : B),
      S.obj.map f (sigma V b) = sigma W b)
    {M N : SheafOfModules.{u + 1} (underlyingRing S)}
    (b : B) (f : M ⟶ N) : M ⟶ N where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        { toFun := fun x ↦ sigma V b • f.val.app V x
          map_add' := fun x y ↦ by rw [map_add, smul_add]
          map_smul' := fun t x ↦ by
            change sigma V b • f.val.app V (t • x) = t • (sigma V b • f.val.app V x)
            rw [(f.val.app V).hom.map_smul]
            change sigma V b • ((t : S.obj.obj V) • f.val.app V x) =
              (t : S.obj.obj V) • (sigma V b • f.val.app V x)
            rw [← mul_smul, ← mul_smul]
            congr 1
            exact mul_comm (sigma V b) (t : S.obj.obj V) }
      naturality := fun {V W} g ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change sigma W b • f.val.app W (M.val.map g x) =
          N.val.map g (sigma V b • f.val.app V x)
        rw [PresheafOfModules.naturality_apply, N.val.map_smul]
        change sigma W b • N.val.map g (f.val.app V x) =
          S.obj.map g (sigma V b) • N.val.map g (f.val.app V x)
        rw [hsigma] }

@[instance_reducible] private def sectionModule {D : Type (u + 1)} [Category.{u} D]
    {K : GrothendieckTopology D}
    (S : Sheaf K CommRingCat.{u + 1}) (B : Type a) [CommRing B]
    (sigma : ∀ V : Dᵒᵖ, B →+* S.obj.obj V)
    (hsigma : ∀ {V W : Dᵒᵖ} (f : V ⟶ W) (b : B),
      S.obj.map f (sigma V b) = sigma W b)
    (M N : SheafOfModules.{u + 1} (underlyingRing S)) :
    Module B (M ⟶ N) where
  smul := sectionScalar S B sigma hsigma
  one_smul f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V 1 • f.val.app V x = f.val.app V x
    rw [map_one, one_smul]
  mul_smul b b' f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V (b * b') • f.val.app V x =
      sigma V b • (sigma V b' • f.val.app V x)
    rw [map_mul, mul_smul]
  smul_zero b := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V b • (0 : N.val.obj V) = 0
    exact smul_zero _
  smul_add b f g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V b • (f.val.app V x + g.val.app V x) =
      sigma V b • f.val.app V x + sigma V b • g.val.app V x
    exact smul_add ..
  add_smul b b' f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V (b + b') • f.val.app V x =
      sigma V b • f.val.app V x + sigma V b' • f.val.app V x
    rw [map_add, add_smul]
  zero_smul f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V 0 • f.val.app V x = 0
    rw [map_zero, zero_smul]

@[instance_reducible] private def sectionLinear {D : Type (u + 1)} [Category.{u} D]
    {K : GrothendieckTopology D}
    (S : Sheaf K CommRingCat.{u + 1}) (B : Type a) [CommRing B]
    (sigma : ∀ V : Dᵒᵖ, B →+* S.obj.obj V)
    (hsigma : ∀ {V W : Dᵒᵖ} (f : V ⟶ W) (b : B),
      S.obj.map f (sigma V b) = sigma W b) :
    Linear B (SheafOfModules.{u + 1} (underlyingRing S)) where
  homModule := sectionModule S B sigma hsigma
  smul_comp M N P b f g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change g.val.app V (sigma V b • f.val.app V x) =
      sigma V b • g.val.app V (f.val.app V x)
    exact (g.val.app V).hom.map_smul _ _
  comp_smul M N P f b g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u + 1})
  (A : Type a) [CommRing A]
  (U : C)
  (rho : ∀ V : Cᵒᵖ, A →+* O.obj.obj V)
  [HasDerivedCategory.{w} (ringedSiteModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u + 1}
    (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O).over U))]
/--
Module extension by zero is additive and linear, and its termwise unbounded derived functor
is linear, commutes with integer shifts, and is triangulated. The `A`-linear structures on
the two module-sheaf categories are the bound ones, pinned by the two sectionwise clauses;
those on the two derived categories are Mathlib's `DerivedCategory.instLinear`, induced from
them by degreewise scalars on cochain maps and localization
(lem-weil-linear-abelian-derived-category). Source: Stacks Project, Modules on Sites,
Tags 03CY, 03DI and 03DJ (blueprint: lem-cbc-localized-extension-zero-linear-derived).
Proof:
1. Define `(a • t)_V(x) = rho V a • t_V(x)` and `(t + t')_V = t_V + t'_V` on module-sheaf
   morphisms; `hnat` makes restriction carry `rho V a` to `rho W a`, and commutativity of
   `O(V)` makes `a • t` linear. Composition is bilinear sectionwise. The same on `C / U`,
   where `O_U(V → U) = O(V)` (def-pur-localized-ringed-site). Both categories are abelian.
2. On the direct-sum extension presheaf (def-weil-extension-by-zero-presheaf),
   `P_{t + t'} = P_t + P_{t'}` and `P_{a • t} = a • P_t` summandwise, for any number of maps
   `V → U`, including none.
3. Functoriality of module sheafification gives `j_! t ∘ η_F = η_G ∘ P_t`; uniqueness of the
   factorization through `η_F` (Stacks 03CY) transfers both identities to `j_!`, so
   `localizedModuleExtension` is additive and `A`-linear.
4. `localizedModuleExtension` is exact (lem-pur-site-restriction-module-adjunction-exact), so
   `mapDerivedCategory` is its termwise unbounded derived functor; Mathlib's instances give
   its shift compatibility and triangulatedness (lem-sf-exact-functor-derived-triangulated).
5. With the induced derived structures (lem-weil-linear-abelian-derived-category), Mathlib's
   `Functor.instLinearDerivedCategoryMapDerivedCategory` applied to Steps 3 and 4 gives
   `A`-linearity of the derived functor on every derived morphism
   (lem-cbc-exact-linear-derived-functor).
-/
theorem localizedExtensionZeroLinearDerived (hnat : ∀ {V W : Cᵒᵖ} (f : V ⟶ W) (a : A),
    O.obj.map f (rho V a) = rho W a) :
    ∃ (_ : Linear A (ringedSiteModules.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))),
      ∃ (_ : Linear A (ringedSiteModules.{u + 1} (((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O).over U))),
        (∀ (M N : ringedSiteModules.{u + 1} ((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
          (f : M ⟶ N) (a : A) (V : Cᵒᵖ) (x : M.val.obj V),
          (a • f).val.app V x = rho V a • f.val.app V x) ∧
        (∀ (M N : ringedSiteModules.{u + 1} (((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O).over U))
          (f : M ⟶ N) (a : A) (V : (Over U)ᵒᵖ) (x : M.val.obj V),
          (a • f).val.app V x =
            rho (Opposite.op V.unop.left) a • f.val.app V x) ∧
        (SheafOfModules.localizedModuleExtension O U).Additive ∧
        Functor.Linear A (SheafOfModules.localizedModuleExtension O U) ∧
        (SheafOfModules.localizedModuleExtension O U).mapDerivedCategory.Additive ∧
        Functor.Linear A (SheafOfModules.localizedModuleExtension O U).mapDerivedCategory ∧
        Nonempty
          ((SheafOfModules.localizedModuleExtension O U).mapDerivedCategory.CommShift ℤ) ∧
        (SheafOfModules.localizedModuleExtension O U).mapDerivedCategory.IsTriangulated := by
  let baseLinear : Linear A (SheafOfModules.{u + 1} (underlyingRing O)) :=
    sectionLinear O A rho hnat
  let OU : Sheaf (J.over U) CommRingCat.{u + 1} := O.over U
  let rhoU : ∀ V : (Over U)ᵒᵖ, A →+* OU.obj.obj V :=
    fun V ↦ rho (op V.unop.left)
  have hnatU : ∀ {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (a : A),
      OU.obj.map f (rhoU V a) = rhoU W a := by
    intro V W f a
    exact hnat ((Over.forget U).op.map f) a
  let sliceLinear : Linear A (SheafOfModules.{u + 1} ((underlyingRing O).over U)) :=
    sectionLinear OU A rhoU hnatU
  have : Functor.Linear A (SheafOfModules.localizedModuleRestriction O U) := by
    constructor
    intro M N f a
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  -- The adjunction transfers linearity, avoiding a second sheafification calculation.
  have : Functor.Linear A (SheafOfModules.localizedModuleExtension O U) :=
    (SheafOfModules.localizedModuleAdjunctionIndependent O U).left_adjoint_linear
  refine ⟨baseLinear, sliceLinear, ?_, ?_, inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨inferInstance⟩, inferInstance⟩
  · intro M N f a V x
    rfl
  · intro M N f a V x
    rfl
end CategoryTheory
