/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule

/-!
# The internal Hom is a sheaf of modules

Source: Stacks Project, Modules on Sites, Sections 04TT and 03DD, Lemma 03EM
and the internal-Hom restriction lemma (blueprint: lem-pur-sheaf-hom-is-sheaf).
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace SheafOfModules

/-- (blueprint: lem-pur-sheaf-hom-is-sheaf) Stacks Project, Modules on Sites,
Section 04TT, Lemma 03EM and the internal-Hom restriction lemma; Section 03DD.
The existing `homObj` uses localized module morphisms, pointwise scalar multiplication,
and relocalization as restriction. It is a sheaf; evaluation at the final object of
`C/U` identifies local global sections with its value at `U`. Its global sections
correspond to module morphisms, compatibly with the global-sections scalar action.

Proof: (1) Restrict module morphisms along relocalization. Multiply by the restricted
ring section; commutativity gives linearity and the restriction maps are semilinear
[def-pur-sheaf-modules-hom-module]. (2) Compatible local linear maps glue uniquely by
[lem-pur-sheaf-hom-cover-gluing]; linearity is local. (3) The final object `U/U` gives
the local-sections identification [def-pur-localized-ringed-site]. (4) Evaluate a
compatible family at `V/V` to obtain the component at `V` of a module morphism.
Compatibility and naturality give a global morphism. Conversely restrict a global
morphism to every `C/U`; these constructions are inverse. Evaluating the pointwise
scalar action at `V/V` proves linearity [def-pur-sheaf-modules-hom-module]. -/
theorem homObj_isSheaf_and_sections
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (hR : Presheaf.IsSheaf J (R ⋙ forget₂ CommRingCat RingCat.{u}))
    (M N : SheafOfModules.{v} ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩) :
    (let H := PresheafOfModules.homObj (R := R) M.val N.val
    Presheaf.IsSheaf J H.presheaf ∧
    (∀ U : C, Function.Bijective
      (fun t : ((⟨H, PresheafOfModules.isSheaf_homObj N.isSheaf⟩ :
          SheafOfModules ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩).over U).sections ↦
        t.1 (op (Over.mk (𝟙 U))))) ∧
    (let e : H.sections ≃ (M ⟶ N) :=
      (PresheafOfModules.homObjSectionsEquiv M.val N.val).trans
        (fullyFaithfulForget _).homEquiv.symm
     Function.Bijective e ∧
     (∀ (φ : M ⟶ N) (U : C),
       (e.symm φ).1 (op U) =
         (PresheafOfModules.restrictOver R U).map φ.val) ∧
     (∀ (t t' t'' : H.sections),
       (∀ X : Cᵒᵖ, t''.1 X = t.1 X + t'.1 X) → e t'' = e t + e t') ∧
     (∀ (s : RingCat.sectionsSubring (R ⋙ forget₂ CommRingCat RingCat.{u}))
         (t : H.sections),
       e (PresheafOfModules.sectionsMap (PresheafOfModules.sectionsSMul H s) t) =
         s • e t))) := by
  -- The source library already proves the sheaf condition via local linearity.
  dsimp only
  refine ⟨PresheafOfModules.isSheaf_homObj N.isSheaf, ?_, ?_⟩
  · intro U
    let H := PresheafOfModules.homObj (R := R) M.val N.val
    refine ⟨?_, ?_⟩
    · intro t t' h
      apply PresheafOfModules.sections_ext
      intro W
      have ht := t.2 (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op
      have ht' := t'.2 (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op
      exact ht.symm.trans ((congrArg (fun x ↦ H.map W.unop.hom.op x) h).trans ht')
    · intro x
      refine ⟨PresheafOfModules.sectionsMk
        (fun W ↦ H.map W.unop.hom.op x) ?_, ?_⟩
      · intro W W' f
        change H.map f.unop.left.op (H.map W.unop.hom.op x) = _
        rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]
      · change H.map (𝟙 U).op x = x
        rw [op_id, H.map_id]
        rfl
  · refine ⟨Equiv.bijective _, ?_, ?_, ?_⟩
    · intro φ U
      rfl
    · intro t t' t'' h
      apply hom_ext
      apply PresheafOfModules.hom_ext
      intro X
      change (t''.1 X).app (op (Over.mk (𝟙 X.unop))) =
        (t.1 X).app (op (Over.mk (𝟙 X.unop))) +
          (t'.1 X).app (op (Over.mk (𝟙 X.unop)))
      rw [h X]
      rfl
    · intro s t
      apply hom_ext
      apply PresheafOfModules.hom_ext
      intro X
      ext x
      change (((show R.obj (op X.unop) from s.1 X) •
        (show (PresheafOfModules.restrictOver R X.unop).obj M.val ⟶
          (PresheafOfModules.restrictOver R X.unop).obj N.val from t.1 X)).app
            (op (Over.mk (𝟙 X.unop)))) x =
        s.1 X • (t.1 X).app (op (Over.mk (𝟙 X.unop))) x
      rw [PresheafOfModules.smul_app]
      change R.map (𝟙 X.unop).op (s.1 X) •
        (t.1 X).app (op (Over.mk (𝟙 X.unop))) x =
          s.1 X • (t.1 X).app (op (Over.mk (𝟙 X.unop))) x
      rw [op_id, R.map_id]
      rfl

end SheafOfModules
