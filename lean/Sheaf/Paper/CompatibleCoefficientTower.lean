/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Compatible coefficient tensor towers

Source: Stacks Project, Modules on Sites, Tags 03EK, 03CY and 03DA;
Homology, Tag 011G (blueprint: lem-pur-compatible-coefficient-tower).

The natural-number index `n` represents the paper's positive index `n + 1`.
The tensor API writes the coefficient factor first, so `z ⊗ x` below is the
paper's `x ⊗ z`. Generators always mean images under the sheafification unit.
-/

@[expose] public section

universe uC vC u uk

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

set_option autoImplicit false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}

/-- Forget commutativity of the coefficient sheaf, using the existing sheaf-composition
functor. Source: Stacks 03EK (blueprint: lem-pur-compatible-coefficient-tower). -/
abbrev coefficientTensorRing (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable {R S : Sheaf J CommRingCat.{u}} {B : ℕ → Sheaf J CommRingCat.{u}}
  (r : ∀ n, R ⟶ B n) (p : ∀ n, S ⟶ B n)

/-- The level module is the existing change of rings followed by restriction of scalars.
Source: Stacks 03EK (blueprint: lem-pur-compatible-coefficient-tower). -/
noncomputable def coefficientTensorLevel (n : ℕ)
    (M : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) :
    ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing S) :=
  (restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (p n))).obj
      (changeOfRings.{vC, uC, u} (r n) M)

/-- Image of a presheaf pure tensor under the sheafification unit. The scalar factor
comes first in the existing change-of-rings API. Source: Stacks 03CY and 03EK
(blueprint: lem-pur-compatible-coefficient-tower). -/
noncomputable def coefficientTowerGenerator (n : ℕ)
    (M : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) (U : Cᵒᵖ)
    (x : M.val.obj U) (z : (B n).obj.obj U) :
    (coefficientTensorLevel r p n M).val.obj U :=
  (toSheafify J (changeOfRingsPresheaf.{vC, uC, u} (r n) M).presheaf).app U
    (z ⊗ₜ[R.obj.obj U, ((r n).hom.app U).hom] x)

/-- Restrict the existing global-sections linear structure along a coefficient map.
This specifies the induced scalar action used in the theorem, without choosing an
arbitrary linear structure. Source: Stacks 03EK, common-scalar calculation
(blueprint: lem-pur-compatible-coefficient-tower). -/
@[instance_reducible]
noncomputable def coefficientTowerScalarLinear (k : Type uk) [CommRing k]
    (T : Sheaf J CommRingCat.{u})
    (a : k →+* RingCat.sectionsSubring (T.obj ⋙ forget₂ CommRingCat RingCat)) :
    Linear k (ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing T)) :=
  letI : Linear (RingCat.sectionsSubring (T.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing T)) :=
    homLinear T.obj (coefficientTensorRing T).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) a
    smul_comp := fun M N P s f g ↦ Linear.smul_comp M N P (a s) f g
    comp_smul := fun M N P f s g ↦ Linear.comp_smul M N P f (a s) g }

/-- The linear-functor predicate with precisely the induced source scalar action and
componentwise induced target scalar action. Source: Stacks 03EK, common-scalar calculation
(blueprint: lem-pur-compatible-coefficient-tower). -/
def CoefficientTowerIsLinear
    (V : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R) ⥤
      (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing S)))
    (k : Type uk) [CommRing k]
    (aR : k →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (aS : k →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat)) : Prop :=
  letI := coefficientTowerScalarLinear k R aR
  letI := coefficientTowerScalarLinear k S aS
  V.Linear k

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

private noncomputable def tensorPreFunctor (a : R ⟶ S) :
    SheafOfModules.{u} (coefficientTensorRing R) ⥤
      PresheafOfModules.{u} (coefficientTensorRing S).obj where
  obj := changeOfRingsPresheaf.{vC, uC, u} a
  map f :=
    { app := fun U ↦ (ModuleCat.extendScalars (a.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality.{vC, uC, u} a _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    simp
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    simp

private instance tensorPreFunctor_additive (a : R ⟶ S) :
    (tensorPreFunctor a).Additive where
  map_add {M N} f g := by
    have h (U : Cᵒᵖ) : (ModuleCat.extendScalars (a.hom.app U).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (a.hom.app U).hom).left_adjoint_additive
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (a.hom.app U).hom).map_add
      (f := f.val.app U) (g := g.val.app U)

private noncomputable def towerPrelevel (n : ℕ) :
    SheafOfModules.{u} (coefficientTensorRing R) ⥤
      PresheafOfModules.{u} (coefficientTensorRing S).obj :=
  tensorPreFunctor (r n) ⋙ PresheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (p n)).hom

private noncomputable def coefficientSheafificationComparison
    {A D : Sheaf J RingCat.{u}} (a : A ⟶ D) (P : PresheafOfModules.{u} D.obj) :
    (PresheafOfModules.sheafification (𝟙 A.obj)).obj
      ((PresheafOfModules.restrictScalars a.hom).obj P) ⟶
        (restrictScalars a).obj ((PresheafOfModules.sheafification (𝟙 D.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 A.obj)).symm
    ((PresheafOfModules.restrictScalars a.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 D.obj)).unit.app P))

set_option backward.isDefEq.respectTransparency.types true in
private theorem coefficientSheafificationComparison_underlying
    {A D : Sheaf J RingCat.{u}} (a : A ⟶ D) (P : PresheafOfModules.{u} D.obj) :
    (toSheaf.{u} A).map (coefficientSheafificationComparison a P) =
      𝟙 ((presheafToSheaf J AddCommGrpCat.{u}).obj P.presheaf) := by
  unfold coefficientSheafificationComparison
  rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm (𝟙 A.obj)]
  change ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
    P.presheaf ((presheafToSheaf J AddCommGrpCat.{u}).obj P.presheaf)).symm
      (toSheafify J P.presheaf) = 𝟙 _
  apply (Equiv.symm_apply_eq _).mpr
  simp only [Adjunction.homEquiv_unit]
  rfl

private instance coefficientSheafificationComparison_isIso
    {A D : Sheaf J RingCat.{u}} (a : A ⟶ D) (P : PresheafOfModules.{u} D.obj) :
    IsIso (coefficientSheafificationComparison a P) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf A),
    coefficientSheafificationComparison_underlying]
  exact IsIso.id ((presheafToSheaf J AddCommGrpCat.{u}).obj P.presheaf)

private theorem coefficientSheafificationComparison_apply
    {A D : Sheaf J RingCat.{u}} (a : A ⟶ D) (P : PresheafOfModules.{u} D.obj)
    (U : Cᵒᵖ) (x : ((PresheafOfModules.sheafification (𝟙 A.obj)).obj
      ((PresheafOfModules.restrictScalars a.hom).obj P)).val.obj U) :
    (coefficientSheafificationComparison a P).val.app U x = x := by
  exact congrArg (fun f ↦ f.hom.app U x)
    (coefficientSheafificationComparison_underlying a P)

private theorem coefficientSheafificationComparison_inv_apply
    {A D : Sheaf J RingCat.{u}} (a : A ⟶ D) (P : PresheafOfModules.{u} D.obj)
    (U : Cᵒᵖ) (x : ((restrictScalars a).obj
      ((PresheafOfModules.sheafification (𝟙 D.obj)).obj P)).val.obj U) :
    (inv (coefficientSheafificationComparison a P)).val.app U x = x := by
  have h := congrArg (fun f ↦ f.val.app U x)
    (IsIso.inv_hom_id (coefficientSheafificationComparison a P))
  change (coefficientSheafificationComparison a P).val.app U
    ((inv (coefficientSheafificationComparison a P)).val.app U x) = x at h
  rw [coefficientSheafificationComparison_apply] at h
  exact h

private noncomputable abbrev towerLevelComparison (n : ℕ)
    (M : SheafOfModules.{u} (coefficientTensorRing R)) :
    (PresheafOfModules.sheafification (𝟙 (coefficientTensorRing S).obj)).obj
      ((towerPrelevel r p n).obj M) ⟶ coefficientTensorLevel r p n M :=
  coefficientSheafificationComparison
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (p n))
    (changeOfRingsPresheaf.{vC, uC, u} (r n) M)

attribute [local irreducible] coefficientSheafificationComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def tensorCoefficientSection
    {T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (d : R ⟶ T) (c : S ⟶ T)
    (h : a ≫ c = d) (M : SheafOfModules.{u} (coefficientTensorRing R)) (U : Cᵒᵖ) :
    (changeOfRingsPresheaf a M).obj U ⟶
      (ModuleCat.restrictScalars (c.hom.app U).hom).obj
        ((changeOfRingsPresheaf d M).obj U) := by
  let : Module (R.obj.obj U) (T.obj.obj U) :=
    Module.compHom (T.obj.obj U) (d.hom.app U).hom
  let N := (ModuleCat.restrictScalars (c.hom.app U).hom).obj
    ((changeOfRingsPresheaf d M).obj U)
  let f : M.val.obj U ⟶ (ModuleCat.restrictScalars (a.hom.app U).hom).obj N :=
    ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (a.hom.app U).hom).obj N)
      { toFun := fun x ↦ (1 : T.obj.obj U) ⊗ₜ[R.obj.obj U, (d.hom.app U).hom] x
        map_add' := by intro x y; simp [TensorProduct.tmul_add]
        map_smul' := by
          intro s x
          have hs : c.hom.app U (a.hom.app U s) = d.hom.app U s :=
            congrArg (fun f : R ⟶ T ↦ f.hom.app U s) h
          change (1 : T.obj.obj U) ⊗ₜ[R.obj.obj U] (s • x) =
            c.hom.app U (a.hom.app U s) •
              ((1 : T.obj.obj U) ⊗ₜ[R.obj.obj U] x)
          rw [hs, TensorProduct.tmul_smul (R' := R.obj.obj U)]
          rfl }
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (a.hom.app U).hom f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorCoefficientSection_tmul
    {T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (d : R ⟶ T) (c : S ⟶ T)
    (h : a ≫ c = d) (M : SheafOfModules.{u} (coefficientTensorRing R)) (U : Cᵒᵖ)
    (z : S.obj.obj U) (x : M.val.obj U) :
    tensorCoefficientSection a d c h M U (z ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) =
      c.hom.app U z ⊗ₜ[R.obj.obj U, (d.hom.app U).hom] x := by
  let : Module (R.obj.obj U) (T.obj.obj U) :=
    Module.compHom (T.obj.obj U) (d.hom.app U).hom
  let N := (ModuleCat.restrictScalars (c.hom.app U).hom).obj
    ((changeOfRingsPresheaf d M).obj U)
  let : Module (R.obj.obj U) N := Module.compHom N (a.hom.app U).hom
  let : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (a.hom.app U).hom
  unfold tensorCoefficientSection
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change c.hom.app U z •
    ((1 : T.obj.obj U) ⊗ₜ[R.obj.obj U, (d.hom.app U).hom] x) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

attribute [local irreducible] tensorCoefficientSection

private theorem tensorAddHom_ext
    {A P Q N : Type*} [CommRing A] [AddCommGroup P] [AddCommGroup Q] [AddCommGroup N]
    [Module A P] [Module A Q] (f g : TensorProduct A P Q →+ N)
    (h : ∀ x y, f (x ⊗ₜ[A] y) = g (x ⊗ₜ[A] y)) : f = g := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => exact h x y
  | add x y hx hy => rw [map_add, map_add, hx, hy]



set_option backward.isDefEq.respectTransparency false in
private noncomputable def towerPretransition
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) (n : ℕ)
    (M : SheafOfModules.{u} (coefficientTensorRing R)) :
    (towerPrelevel r p (n + 1)).obj M ⟶ (towerPrelevel r p n).obj M where
  app U := ModuleCat.ofHom
    (X := ((towerPrelevel r p (n + 1)).obj M).obj U)
    (Y := ((towerPrelevel r p n).obj M).obj U)
    { toFun := tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U
      map_add' := map_add _
      map_smul' := by
        intro s x
        have hs : (b n).hom.app U ((p (n + 1)).hom.app U s) = (p n).hom.app U s :=
          congrArg (fun f : S ⟶ B n ↦ f.hom.app U s) (hp n)
        change tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U
          (((p (n + 1)).hom.app U s) •
            (show (changeOfRingsPresheaf.{vC, uC, u} (r (n + 1)) M).obj U from x)) = _
        rw [map_smul]
        change (b n).hom.app U ((p (n + 1)).hom.app U s) •
          (show (changeOfRingsPresheaf.{vC, uC, u} (r n) M).obj U from
            tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U x) = _
        rw [hs]
        rfl }
  naturality {U V} f := by
    suffices h :
        (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M V).hom.toAddMonoidHom.comp
          (changeOfRingsMap (r (n + 1)) M f).hom.toAddMonoidHom =
        (changeOfRingsMap (r n) M f).hom.toAddMonoidHom.comp
          (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U).hom.toAddMonoidHom by
      ext t
      exact DFunLike.congr_fun h t
    apply tensorAddHom_ext
    intro z x
    change tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M V
      (changeOfRingsMap (r (n + 1)) M f (z ⊗ₜ x)) =
        changeOfRingsMap (r n) M f
          (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U (z ⊗ₜ x))
    rw [show changeOfRingsMap (r (n + 1)) M f (z ⊗ₜ x) = _ from
      Classical.choose_spec (exists_changeOfRingsMap (r (n + 1)) M f) z x]
    rw [tensorCoefficientSection_tmul, tensorCoefficientSection_tmul]
    rw [show changeOfRingsMap (r n) M f
      ((b n).hom.app U z ⊗ₜ[R.obj.obj U, ((r n).hom.app U).hom] x) = _ from
      Classical.choose_spec (exists_changeOfRingsMap (r n) M f) ((b n).hom.app U z) x]
    congr 1
    exact ConcreteCategory.congr_hom ((b n).hom.naturality f) z

private theorem towerPretransition_naturality
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) (n : ℕ)
    {M N : SheafOfModules.{u} (coefficientTensorRing R)} (f : M ⟶ N) :
    towerPretransition r p b hr hp n M ≫ (towerPrelevel r p n).map f =
      (towerPrelevel r p (n + 1)).map f ≫ towerPretransition r p b hr hp n N := by
  apply PresheafOfModules.hom_ext
  intro U
  suffices h :
      ((ModuleCat.extendScalars ((r n).hom.app U).hom).map
        (f.val.app U)).hom.toAddMonoidHom.comp
          (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U).hom.toAddMonoidHom =
      (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) N U).hom.toAddMonoidHom.comp
        ((ModuleCat.extendScalars ((r (n + 1)).hom.app U).hom).map
          (f.val.app U)).hom.toAddMonoidHom by
    ext t
    exact DFunLike.congr_fun h t
  apply tensorAddHom_ext
  intro z x
  change (ModuleCat.extendScalars ((r n).hom.app U).hom).map (f.val.app U)
    (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U (z ⊗ₜ x)) =
      tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) N U
        ((ModuleCat.extendScalars ((r (n + 1)).hom.app U).hom).map
          (f.val.app U) (z ⊗ₜ x))
  rw [tensorCoefficientSection_tmul]
  erw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.ExtendScalars.map_tmul]
  rw [tensorCoefficientSection_tmul]

private noncomputable def towerTransition
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) (n : ℕ) :
    towerPrelevel r p (n + 1) ⋙ PresheafOfModules.sheafification
      (𝟙 (coefficientTensorRing S).obj) ⟶
        towerPrelevel r p n ⋙ PresheafOfModules.sheafification
          (𝟙 (coefficientTensorRing S).obj) where
  app M := (PresheafOfModules.sheafification
    (𝟙 (coefficientTensorRing S).obj)).map (towerPretransition r p b hr hp n M)
  naturality {M N} f := by
    symm
    change (PresheafOfModules.sheafification (𝟙 (coefficientTensorRing S).obj)).map
      (towerPretransition r p b hr hp n M) ≫
        (PresheafOfModules.sheafification (𝟙 (coefficientTensorRing S).obj)).map
          ((towerPrelevel r p n).map f) = _
    simp only [Functor.comp_map, ← Functor.map_comp]
    rw [towerPretransition_naturality r p b hr hp]

private noncomputable def towerFunctor
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) :
    SheafOfModules.{u} (coefficientTensorRing R) ⥤
      (ℕᵒᵖ ⥤ SheafOfModules.{u} (coefficientTensorRing S)) :=
  (Functor.ofOpSequence
    (X := fun n ↦ towerPrelevel r p n ⋙ PresheafOfModules.sheafification
      (𝟙 (coefficientTensorRing S).obj)) (towerTransition r p b hr hp)).flip

private instance towerFunctor_additive
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) :
    (towerFunctor r p b hr hp).Additive where
  map_add {M N} f g := by
    have : (PresheafOfModules.sheafification
        (𝟙 (coefficientTensorRing S).obj)).Additive :=
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (coefficientTensorRing S).obj)).left_adjoint_additive
    have (n : ℕ) : (towerPrelevel r p n).Additive := by
      unfold towerPrelevel
      infer_instance
    apply NatTrans.ext
    funext n
    exact ((towerPrelevel r p n.unop) ⋙ PresheafOfModules.sheafification
      (𝟙 (coefficientTensorRing S).obj)).map_add (f := f) (g := g)

private theorem quasiIso_iff_map_of_comp
    {A D E : Type*} [Category A] [Category D] [Category E]
    [Abelian A] [Abelian D] [Abelian E]
    (U : A ⥤ D) (F : D ⥤ E) [U.Additive] [F.Additive]
    [F.PreservesHomology] [F.ReflectsIsomorphisms]
    [(U ⋙ F).PreservesHomology] [(U ⋙ F).ReflectsIsomorphisms]
    (K L : CochainComplex A ℤ) (f : K ⟶ L) :
    QuasiIso ((U.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ↔ QuasiIso f := by
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((U.mapHomologicalComplex (ComplexShape.up ℤ)).map f) F).symm.trans
      (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f (U ⋙ F))

private theorem restrictScalars_quasiIso_iff (a : R ⟶ S)
    (K L : CochainComplex (SheafOfModules.{u} (coefficientTensorRing S)) ℤ)
    (f : K ⟶ L) :
    QuasiIso (((restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map a)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) ↔ QuasiIso f := by
  let U := restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map a)
  let UR := toSheaf.{u} (coefficientTensorRing R)
  let US := toSheaf.{u} (coefficientTensorRing S)
  have : PreservesFiniteColimits UR :=
    (moduleSheaves_colimits_forgetful (coefficientTensorRing R)).2.2.1
  have : PreservesFiniteColimits US :=
    (moduleSheaves_colimits_forgetful (coefficientTensorRing S)).2.2.1
  have : (U ⋙ UR).PreservesHomology := inferInstanceAs US.PreservesHomology
  have : (U ⋙ UR).ReflectsIsomorphisms := inferInstanceAs US.ReflectsIsomorphisms
  exact quasiIso_iff_map_of_comp U UR K L f

private theorem sheafification_map_unit
    {A : Sheaf J RingCat.{u}} {P Q : PresheafOfModules.{u} A.obj} (f : P ⟶ Q)
    (U : Cᵒᵖ) (x : P.obj U) :
    ((PresheafOfModules.sheafification (𝟙 A.obj)).map f).val.app U
      ((toSheafify J P.presheaf).app U x) = (toSheafify J Q.presheaf).app U (f.app U x) := by
  exact (congrArg (fun t ↦ t.app U x)
    (toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map f))).symm

private theorem towerTensor_hom_ext (n : ℕ)
    (M : SheafOfModules.{u} (coefficientTensorRing R))
    {N : SheafOfModules.{u} (coefficientTensorRing S)}
    {f g : coefficientTensorLevel r p n M ⟶ N}
    (h : ∀ U x z, f.val.app U (coefficientTowerGenerator r p n M U x z) =
      g.val.app U (coefficientTowerGenerator r p n M U x z)) : f = g := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply sheafify_hom_ext J _ _ N.isSheaf
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply tensorAddHom_ext
  intro z x
  exact h U x z

private theorem towerSheaf_hom_ext (n : ℕ)
    (M : SheafOfModules.{u} (coefficientTensorRing R))
    {N : SheafOfModules.{u} (coefficientTensorRing S)}
    {f g : (PresheafOfModules.sheafification
      (𝟙 (coefficientTensorRing S).obj)).obj ((towerPrelevel r p n).obj M) ⟶ N}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (z : (B n).obj.obj U),
      f.val.app U ((toSheafify J ((towerPrelevel r p n).obj M).presheaf).app U
        (z ⊗ₜ[R.obj.obj U,((r n).hom.app U).hom] x)) =
      g.val.app U ((toSheafify J ((towerPrelevel r p n).obj M).presheaf).app U
        (z ⊗ₜ[R.obj.obj U,((r n).hom.app U).hom] x))) : f = g := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply sheafify_hom_ext J _ _ N.isSheaf
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply tensorAddHom_ext
  intro z x
  exact h U x z

/-- Compatible coefficient maps give an additive strict tensor tower, compatible with
homotopies, integer shifts and common scalars.

Source: Stacks 03EK (section-tensor-product), 03CY
(lemma-sheafification-presheaf-modules), 03DA (lemma-abelian), and Homology 011G
(definition-shift-cochain), with the agent-written strict-tower refinement
(blueprint: lem-pur-compatible-coefficient-tower).

Proof plan, following the node:
1. The balancing relation and the two coefficient compatibilities make
   `x ⊗ z ↦ x ⊗ b_n(z)` a natural map of presheaves of S-modules.
2. Apply lem-pc-sites-module-sheafification-interface and def-weil-pbc-sheafification.
   Sheafifying after restriction has the same abelian sheafification and the same
   extended S-action. The unit and pure tensors therefore determine a unique sheaf map.
3. The maps `f ⊗ 1` commute with transitions: both composites send a generator to
   `f(x) ⊗ b_n(z)`. Identity, composition and addition follow on the same generators.
4. Assemble adjacent transitions with def-weil-inverse-system. Functor laws and
   additivity hold componentwise; all longer transitions are the prescribed composites.
5. Apply this additive functor degreewise. Applying it to the homotopy equation
   gives the termwise image homotopy (def-weil-abstract-derived-category).
6. The integer-shift comparison is the identity in each degree. Additivity preserves
   the sign in the differential. Its tower naturality gives compatibility with every
   transition. Zero and addition coherence follow from identity components and reindexing.
7. By lem-weil-pbc-module-sheaves-colimits-forgetful, the two forgetful functors to
   abelian sheaves preserve kernels and cokernels. Restriction changes neither the
   underlying abelian sheaf nor its cohomology.
8. An inverse of an invertible underlying abelian-sheaf map is module-linear.
   Thus restriction preserves and reflects quasi-isomorphisms; no tensor flatness is used.
9. Global sections induce the displayed linear structures. On pure tensors, balancing
   and the equality of the two images of each scalar show `V(a f) = a V(f)`.

The level isomorphisms identify the values with the specified tensor modules, rather
than asking that two presentations of the same sheaf be definitionally equal. Uniqueness
is asserted for maps of those actual tensor modules, tested on presheaf generators.
The shift comparison is a morphism of towers, so its naturality already includes the
transition squares; its identity components fix the termwise comparison uniquely. -/
theorem exists_compatibleCoefficientTower
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) :
    ∃ V : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R) ⥤
        (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing S)),
      ∃ e : ∀ (M : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) (n : ℕ),
        (V.obj M).obj (op n) ≅ coefficientTensorLevel r p n M,
      ∃ (_hV : V.Additive),
        (∀ (M : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) (n : ℕ),
          (∀ (U : Cᵒᵖ) (x : M.val.obj U) (z : (B (n + 1)).obj.obj U),
            (((e M (n + 1)).inv ≫
                (V.obj M).map (homOfLE (Nat.le_succ n)).op ≫ (e M n).hom).val.app U)
              (coefficientTowerGenerator r p (n + 1) M U x z) =
              coefficientTowerGenerator r p n M U x (((b n).hom.app U) z)) ∧
          (∀ t : coefficientTensorLevel r p (n + 1) M ⟶ coefficientTensorLevel r p n M,
            (∀ (U : Cᵒᵖ) (x : M.val.obj U) (z : (B (n + 1)).obj.obj U),
              t.val.app U (coefficientTowerGenerator r p (n + 1) M U x z) =
                coefficientTowerGenerator r p n M U x (((b n).hom.app U) z)) →
            t = (e M (n + 1)).inv ≫
              (V.obj M).map (homOfLE (Nat.le_succ n)).op ≫ (e M n).hom)) ∧
        (∀ (M N : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R))
          (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U) (z : (B n).obj.obj U),
          (((e M n).inv ≫ (V.map f).app (op n) ≫ (e N n).hom).val.app U)
              (coefficientTowerGenerator r p n M U x z) =
            coefficientTowerGenerator r p n N U (f.val.app U x) z) ∧
        (∀ (K L : CochainComplex
            (ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) ℤ)
          (f g : K ⟶ L), Homotopy f g →
          Nonempty (Homotopy ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map g))) ∧
        (∃ cs : (V.mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ,
          ∀ (K : CochainComplex
              (ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) ℤ) (a i : ℤ),
            ((cs.commShiftIso a).hom.app K).f i = 𝟙 _) ∧
        (∀ (n : ℕ) (K L : CochainComplex
            (ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing (B n))) ℤ)
          (f : K ⟶ L),
          QuasiIso (((restrictScalars.{u}
            ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).map (p n))).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f) ↔ QuasiIso f) ∧
        (∀ (k : Type uk) [CommRing k]
          (aR : k →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
          (aS : k →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat)),
          (∀ (n : ℕ) (a : k) (U : Cᵒᵖ),
            ((r n).hom.app U) ((aR a).val U) = ((p n).hom.app U) ((aS a).val U)) →
          CoefficientTowerIsLinear V k aR aS) := by
  let V := towerFunctor r p b hr hp
  let e (M : SheafOfModules.{u} (coefficientTensorRing R)) (n : ℕ) :
      (V.obj M).obj (op n) ≅ coefficientTensorLevel r p n M :=
    asIso (towerLevelComparison r p n M)
  have : V.Additive := inferInstance
  have ht (M : SheafOfModules.{u} (coefficientTensorRing R)) (n : ℕ)
      (U : Cᵒᵖ) (x : M.val.obj U) (z : (B (n + 1)).obj.obj U) :
      (((e M (n + 1)).inv ≫
        (V.obj M).map (homOfLE (Nat.le_succ n)).op ≫ (e M n).hom).val.app U)
          (coefficientTowerGenerator r p (n + 1) M U x z) =
        coefficientTowerGenerator r p n M U x (((b n).hom.app U) z) := by
    change (towerLevelComparison r p n M).val.app U
      (((((Functor.ofOpSequence
        (X := fun m ↦ towerPrelevel r p m ⋙ PresheafOfModules.sheafification
          (𝟙 (coefficientTensorRing S).obj)) (towerTransition r p b hr hp)).map
            (homOfLE (Nat.le_succ n)).op).app M).val.app U)
              ((inv (towerLevelComparison r p (n + 1) M)).val.app U _)) = _
    erw [coefficientSheafificationComparison_apply
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (p n))
      (changeOfRingsPresheaf.{vC, uC, u} (r n) M) U,
      coefficientSheafificationComparison_inv_apply
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (p (n + 1)))
        (changeOfRingsPresheaf.{vC, uC, u} (r (n + 1)) M) U]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    change ((PresheafOfModules.sheafification
      (𝟙 (coefficientTensorRing S).obj)).map
      (towerPretransition r p b hr hp n M)).val.app U
        ((toSheafify J ((towerPrelevel r p (n + 1)).obj M).presheaf).app U _) = _
    rw [sheafification_map_unit]
    change (toSheafify J ((towerPrelevel r p n).obj M).presheaf).app U
      (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U (z ⊗ₜ x)) = _
    rw [tensorCoefficientSection_tmul]
    rfl
  refine ⟨V, e, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M n
    refine ⟨ht M n, ?_⟩
    intro t h
    apply towerTensor_hom_ext r p (n + 1) M
    intro U x z
    exact (h U x z).trans (ht M n U x z).symm
  · intro M N f n U x z
    change (towerLevelComparison r p n N).val.app U
      (((PresheafOfModules.sheafification (𝟙 (coefficientTensorRing S).obj)).map
        ((towerPrelevel r p n).map f)).val.app U
          ((inv (towerLevelComparison r p n M)).val.app U _)) = _
    erw [coefficientSheafificationComparison_apply
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (p n))
      (changeOfRingsPresheaf.{vC, uC, u} (r n) N) U,
      coefficientSheafificationComparison_inv_apply
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (p n))
        (changeOfRingsPresheaf.{vC, uC, u} (r n) M) U]
    change ((PresheafOfModules.sheafification
      (𝟙 (coefficientTensorRing S).obj)).map ((towerPrelevel r p n).map f)).val.app U
        ((toSheafify J ((towerPrelevel r p n).obj M).presheaf).app U _) = _
    rw [sheafification_map_unit]
    change (toSheafify J ((towerPrelevel r p n).obj N).presheaf).app U
      ((ModuleCat.extendScalars ((r n).hom.app U).hom).map (f.val.app U) (z ⊗ₜ x)) = _
    erw [ModuleCat.ExtendScalars.map_tmul]
    rfl
  · intro K L f g h
    exact ⟨V.mapHomotopy h⟩
  · refine ⟨inferInstance, ?_⟩
    intro K a i
    exact V.mapHomologicalComplex_commShiftIso_hom_app_f K a i
  · intro n K L f
    exact restrictScalars_quasiIso_iff (p n) K L f
  · intro k _ aR aS hscalar
    let := coefficientTowerScalarLinear k R aR
    let := coefficientTowerScalarLinear k S aS
    change V.Linear k
    refine ⟨?_⟩
    intro M N f a
    apply NatTrans.ext
    funext n
    apply towerSheaf_hom_ext r p n.unop M
    intro U x z
    change (((V.map (a • f)).app n).val.app U) _ =
      ((a • V.map f).app n).val.app U _
    change ((PresheafOfModules.sheafification
      (𝟙 (coefficientTensorRing S).obj)).map
        ((towerPrelevel r p n.unop).map (a • f))).val.app U
          ((toSheafify J ((towerPrelevel r p n.unop).obj M).presheaf).app U _) = _
    rw [sheafification_map_unit]
    change (toSheafify J ((towerPrelevel r p n.unop).obj N).presheaf).app U
      ((ModuleCat.extendScalars ((r n.unop).hom.app U).hom).map
        ((a • f).val.app U) (z ⊗ₜ x)) = _
    erw [ModuleCat.ExtendScalars.map_tmul]
    change (toSheafify J ((towerPrelevel r p n.unop).obj N).presheaf).app U
      (z ⊗ₜ[R.obj.obj U, ((r n.unop).hom.app U).hom]
        ((aR a).val U • f.val.app U x)) =
      (aS a).val U • (((V.map f).app n).val.app U
        ((toSheafify J ((towerPrelevel r p n.unop).obj M).presheaf).app U _))
    change _ = (aS a).val U •
      (((PresheafOfModules.sheafification (𝟙 (coefficientTensorRing S).obj)).map
        ((towerPrelevel r p n.unop).map f)).val.app U
          ((toSheafify J ((towerPrelevel r p n.unop).obj M).presheaf).app U _))
    rw [sheafification_map_unit]
    let η := (PresheafOfModules.sheafificationAdjunction
      (𝟙 (coefficientTensorRing S).obj)).unit.app ((towerPrelevel r p n.unop).obj N)
    change η.app U (z ⊗ₜ[R.obj.obj U, ((r n.unop).hom.app U).hom]
      ((aR a).val U • f.val.app U x)) =
        (aS a).val U • (η.app U
          ((ModuleCat.extendScalars ((r n.unop).hom.app U).hom).map
            (f.val.app U) (z ⊗ₜ x)))
    erw [ModuleCat.ExtendScalars.map_tmul]
    rw [← (η.app U).hom.map_smul]
    congr 1
    change z ⊗ₜ[R.obj.obj U, ((r n.unop).hom.app U).hom]
      ((aR a).val U • f.val.app U x) =
        (p n.unop).hom.app U ((aS a).val U) •
          (z ⊗ₜ[R.obj.obj U, ((r n.unop).hom.app U).hom] f.val.app U x)
    let : Module (R.obj.obj U) ((B n.unop).obj.obj U) :=
      Module.compHom _ ((r n.unop).hom.app U).hom
    rw [TensorProduct.tmul_smul (R' := R.obj.obj U)]
    change (((r n.unop).hom.app U ((aR a).val U)) * z) ⊗ₜ[R.obj.obj U]
      f.val.app U x = _
    rw [hscalar]
    rfl

end SheafOfModules
