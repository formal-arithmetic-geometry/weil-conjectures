/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects

/-! # Affine section comparisons for coherent formal modules

Source: Stacks Project, Lemmas 087W and 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false in
private def sectionsIso {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) :
    (ModuleCat.restrictScalars U.topIso.inv.hom).obj
      ((SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤)).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≅
      (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj M := by
  let j := M.restrictAppIso U.ι ⊤ ≪≫
    M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
  let S : ModuleCat Γ(X, U) := (ModuleCat.restrictScalars U.topIso.inv.hom).obj
    ((SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤)).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj M))
  let Q : ModuleCat Γ(X, U) := (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj M
  let a : S ≃+ Q := j.addCommGroupIsoToAddEquiv
  let l : S ≃ₗ[Γ(X, U)] Q :=
    { __ := a
      map_smul' := by
        intro r x
        change j.hom (U.topIso.inv r • x) = r • j.hom x
        dsimp [j]
        rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
        change M.presheaf.map (eqToHom U.ι_image_top.symm).op
          ((U.ι.appIso ⊤).inv (U.topIso.inv r) •
            (M.restrictAppIso U.ι ⊤).hom x) =
          r • M.presheaf.map (eqToHom U.ι_image_top.symm).op
            ((M.restrictAppIso U.ι ⊤).hom x)
        rw [Scheme.Modules.map_smul]
        congr 1
        simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
        change X.presheaf.map (eqToHom U.ι_image_top.symm).op
          (X.presheaf.map (eqToHom U.ι_image_top).op r) = r
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        simp }
  exact l.toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- Termwise restriction identifies affine sections as A-module diagrams.
Source: Stacks Project, Lemma 087X, restriction to an affine open. -/
theorem coherentFormalModule_affine_limit_comparison
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) (V : X.affineOpens)
    [IsNoetherian V.1.toScheme] :
    Nonempty
      (((IsCoherentFormalModule I).ι ⋙
          (Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat Γ(X, V.1))).obj
            (SheafOfModules.evaluation X.ringCatSheaf (op V.1))) ≅
        coherentFormalModulesRestriction I V.1 ⋙
          (IsCoherentFormalModule (I.comap V.1.ι)).ι ⋙
          (Functor.whiskeringRight ℕᵒᵖ V.1.toScheme.Modules (ModuleCat Γ(X, V.1))).obj
            (SheafOfModules.evaluation V.1.toScheme.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars V.1.topIso.inv.hom)) := by
  classical
  let e : SheafOfModules.evaluation X.ringCatSheaf (op V.1) ≅
      Scheme.Modules.restrictFunctor V.1.ι ⋙
        SheafOfModules.evaluation V.1.toScheme.ringCatSheaf (op ⊤) ⋙
          ModuleCat.restrictScalars V.1.topIso.inv.hom :=
    NatIso.ofComponents (fun M ↦ (sectionsIso V.1 M).symm) (by
      intro M N f
      ext x
      dsimp [sectionsIso]
      change (Scheme.Modules.presheaf N).map (eqToHom V.1.ι_image_top).op
        (Scheme.Modules.Hom.app f V.1 x) =
        Scheme.Modules.Hom.app f (V.1.ι ''ᵁ ⊤)
          ((Scheme.Modules.presheaf M).map (eqToHom V.1.ι_image_top).op x)
      exact ConcreteCategory.congr_hom
        ((Scheme.Modules.Hom.mapPresheaf f).naturality (eqToHom V.1.ι_image_top).op).symm x)
  refine ⟨?_⟩
  exact NatIso.ofComponents
    (fun F ↦ Functor.isoWhiskerLeft F.obj e) (by
      intro F G f
      apply NatTrans.ext
      funext n
      exact e.hom.naturality (f.hom.app n))

end

end AlgebraicGeometry
