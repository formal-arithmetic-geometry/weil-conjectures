/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Mathlib.Algebra.Module.ZMod

/-! # Cyclic coefficients on a sheaf annihilated by an integer

Source: Stacks Project, Tag 0F1I, passage to Z/nZ coefficients.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- A sheaf killed by `n` has its canonical cyclic coefficient structure.
Source: Stacks Project, Tag 0F1I (blueprint: lem-kun-n-torsion-module-lift).

Proof: on each group of sections use the canonical Z/nZ action. Every additive
restriction map is linear for this action. Restrict scalars along the universe-lift
ring equivalence. The underlying group presheaf is unchanged, so the sheaf condition
follows by the forgetful functors to types. Forgetting the resulting module sheaf
recovers the original sheaf, with identity components. -/
theorem exists_moduleLift_of_nsmul_eq_zero {T : Scheme.{u}} (n : ℕ)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : n • 𝟙 F = 0) :
    ∃ G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))),
      Nonempty ((moduleAbelianForget (ULift.{u + 1} (ZMod n)) T).obj G ≅ F) := by
  have hn (V : T.Etaleᵒᵖ) (x : F.obj.obj V) : n • x = 0 := by
    let E := sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation T.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj V
    have h := congrArg E.map hF
    simp only [Functor.map_nsmul, Functor.map_zero] at h
    simpa using congrArg (fun α ↦ α.hom x) h
  let (V : T.Etaleᵒᵖ) : Module (ZMod n) (F.obj.obj V) :=
    AddCommGroup.zmodModule (hn V)
  let P : T.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n) :=
    { obj := fun V ↦ ModuleCat.of (ZMod n) (F.obj.obj V)
      map := fun α ↦ ModuleCat.ofHom ((F.obj.map α).hom.toZModLinearMap n)
      map_id := by intro V; ext x; exact congrArg (fun k ↦ k.hom x) (F.obj.map_id V)
      map_comp := by
        intro V W Z α β
        ext x
        exact congrArg (fun k ↦ k.hom x) (F.obj.map_comp α β) }
  let Q := P ⋙ ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{u + 1} (ZMod n) ≃+* ZMod n).toRingHom
  have hQ : Presheaf.IsSheaf T.smallEtaleTopology Q := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget T.smallEtaleTopology Q
      (forget (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))]
    exact (Presheaf.isSheaf_iff_isSheaf_forget T.smallEtaleTopology F.obj
      (forget AddCommGrpCat.{u + 1})).mp F.property
  refine ⟨⟨Q, hQ⟩, ⟨?_⟩⟩
  exact ObjectProperty.isoMk _ (Iso.refl F.obj)

end AlgebraicGeometry.Etale
