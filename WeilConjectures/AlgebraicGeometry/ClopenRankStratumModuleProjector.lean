/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
import WeilConjectures.AlgebraicGeometry.SchemeClopenIdempotent

/-! # The characteristic idempotent acts on module sheaves

## References

* Stacks Project, Tag 00EE (clopen idempotents)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def ringedScalar (X : RingedSpace.{u})
    (s : ∀ U : (Opens X)ᵒᵖ, X.presheaf.obj U)
    (hs : ∀ {U V : (Opens X)ᵒᵖ} (f : U ⟶ V), X.presheaf.map f (s U) = s V) :
    𝟭 (SheafOfModules.{u} (moduleRings X)) ⟶
      𝟭 (SheafOfModules.{u} (moduleRings X)) where
  app M :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          (show M.val.obj U →ₗ[(moduleRings X).obj.obj U] M.val.obj U from
            { toFun := fun x ↦ (s U : (moduleRings X).obj.obj U) • x
              map_add' := fun x y ↦ smul_add _ _ _
              map_smul' := fun c x ↦ by
                rw [← mul_smul, ← mul_smul]
                congr 1
                exact mul_comm (s U) c })
        naturality := by
          intro U V f
          ext x
          change s V • (show M.val.obj V from M.val.map f x) =
            M.val.map f (s U • x)
          rw [M.val.map_smul]
          have h := hs f
          change (moduleRings X).obj.map f (s U) = s V at h
          rw [h] } }
  naturality := by
    intro M N f
    ext U x
    exact ((f.val.app U).hom.map_smul (s U) x).symm

set_option backward.isDefEq.respectTransparency false in
/-- The characteristic idempotent of a rank stratum acts naturally on all
modules over the direct-image algebra. It is the identity on modules pushed
forward from that stratum and zero on modules from any other rank stratum
(Stacks, Tag 00EE). -/
theorem clopenRankStratum_module_projector
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (r : LocallyConstant Z ℕ) (q : ℕ) :
    ∃ η : 𝟭 (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) ⟶
        𝟭 (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))),
      η ≫ η = η ∧
      ∀ (k : ℕ) (F : (Scheme.Modules.exteriorRankOpen r k).toScheme.Modules),
        η.app ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj
          ((Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r k).ι).obj F)) =
        if k = q then 𝟙 _ else 0 := by
  classical
  obtain ⟨e, he, _⟩ := (scheme_clopen_idempotent Z).2.2.1
    ⟨{x | r x = q}, r.isLocallyConstant.isOpen_fiber q,
      r.isLocallyConstant.isClosed_fiber q⟩
  let s : ∀ V : (Opens (directImageAlgebraSpace i))ᵒᵖ,
      (directImageAlgebraSpace i).presheaf.obj V := fun V ↦
    Z.presheaf.map (homOfLE
      (show (Opens.map i.base).obj V.unop ≤ ⊤ from le_top)).op e
  have hs : ∀ {U V : (Opens (directImageAlgebraSpace i))ᵒᵖ} (f : U ⟶ V),
      (directImageAlgebraSpace i).presheaf.map f (s U) = s V := by
    intro U V f
    change Z.presheaf.map _ (Z.presheaf.map _ e) = Z.presheaf.map _ e
    rw [← CommRingCat.comp_apply, ← Z.presheaf.map_comp]
    rfl
  refine ⟨ringedScalar (directImageAlgebraSpace i) s hs, ?_, ?_⟩
  · ext M U x
    dsimp [ringedScalar, s]
    change (Z.presheaf.map (homOfLE
      (show (Opens.map i.base).obj U.unop ≤ ⊤ from le_top)).op e) •
        ((Z.presheaf.map (homOfLE
          (show (Opens.map i.base).obj U.unop ≤ ⊤ from le_top)).op e) • x) = _
    rw [← mul_smul, ← map_mul, he.1.eq]
  · intro k F
    let U := Scheme.Modules.exteriorRankOpen r k
    let j := U.ι
    have hres (V : Z.Opens) (hV : V ≤ U) :
        Z.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op e =
          if k = q then 1 else 0 := by
      apply TopCat.Presheaf.section_ext Z.sheaf V
      intro x hx
      change Z.presheaf.germ V x hx (Z.presheaf.map _ e) =
        Z.presheaf.germ V x hx _
      rw [← CommRingCat.comp_apply, Z.presheaf.germ_res]
      change Z.presheaf.Γgerm x e = _
      have hr : r x = k := hV hx
      by_cases hk : k = q
      · rw [ite_eq_left hk, map_one]
        exact he.2.1 x (hr.trans hk)
      · rw [ite_eq_right hk, map_zero]
        exact he.2.2 x (fun hxq ↦ hk (hr.symm.trans hxq))
    have hscalar (V : Z.Opens) :
        j.app V (Z.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op e) =
          if k = q then 1 else 0 := by
      rw [Scheme.Opens.ι_app, ← CommRingCat.comp_apply, ← Functor.map_comp]
      change Z.presheaf.map (homOfLE
        (show j ''ᵁ j ⁻¹ᵁ V ≤ ⊤ from le_top)).op e = _
      apply hres
      rintro x ⟨y, hy, rfl⟩
      exact y.property
    by_cases hk : k = q
    · rw [ite_eq_left hk]
      ext V x
      dsimp [ringedScalar, s]
      change (j.app ((Opens.map i.base).obj V.unop)
        (Z.presheaf.map (homOfLE
          (show (Opens.map i.base).obj V.unop ≤ ⊤ from le_top)).op e)) •
          (show F.val.obj (op (j ⁻¹ᵁ (Opens.map i.base).obj V.unop)) from x) = x
      rw [hscalar, ite_eq_left hk, one_smul]
    · rw [ite_eq_right hk]
      ext V x
      dsimp [ringedScalar, s]
      change (j.app ((Opens.map i.base).obj V.unop)
        (Z.presheaf.map (homOfLE
          (show (Opens.map i.base).obj V.unop ≤ ⊤ from le_top)).op e)) •
          (show F.val.obj (op (j ⁻¹ᵁ (Opens.map i.base).obj V.unop)) from x) = 0
      rw [hscalar, ite_eq_right hk, zero_smul]

end AlgebraicGeometry
