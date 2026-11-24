/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix

import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm

/-!
# Local freeness of cokernels of continuous matrices of locally constant rank

## References

* Hemo–Richarz–Scholbach, Example 3.1
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A finite presentation matrix of locally constant pointwise rank has locally free
cokernel over continuous field-valued coefficients, with no noetherian hypothesis
(Hemo–Richarz–Scholbach, Example 3.1). -/
theorem exists_finiteFree_cover_cokernel_of_locallyConstant_rank
    (E : Type u) [NormedField E] (V : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E)) [IsIso e] [IsMonHom e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n)
    (hr : IsLocallyConstant (fun v : V ↦
      ((continuousFieldPresentationMatrix E V e f).map (fun a ↦ a v)).rank)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage V, ∀ i : C.I₀,
      Mod.IsFree ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj R)
        (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod R).obj (cokernel f)) := by
  obtain ⟨C, hC⟩ := exists_cover_continuousField_presentation_normalForm E V R e f hr
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨r, s, t, a, b, h⟩ := hC i
  let F := (upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod R
  let T := (upperStar AddCommGrpCat.{u + 1} (C.f i)).obj R
  let k : Mod.finiteFree T r ⊞ Mod.finiteFree T s ⟶
      Mod.finiteFree T r ⊞ Mod.finiteFree T t := biprod.map (𝟙 _) 0
  have hk : k = biprod.fst ≫ biprod.inl := by
    apply biprod.hom_ext <;> simp [k]
  refine ⟨t, ⟨PreservesCokernel.iso F f ≪≫ cokernel.mapIso (F.map f) k a b ?_ ≪≫
    cokernelIsoOfEq hk ≪≫ cokernelEpiComp _ _ ≪≫ cokernelBiprodInlIso⟩⟩
  change F.map f ≫ b.hom = a.hom ≫ k
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale
