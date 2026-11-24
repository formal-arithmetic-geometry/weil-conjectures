/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.StalkTensorMultiplicationRange
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealStalkRange
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitStalkKernelOnImage

/-! # Stalk kernel calculation for a closed immersion

## References

* Stacks Project, Tags 08KS, 0098 and 00AE
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option backward.isDefEq.respectTransparency false in
private theorem unit_stalk_iso (X : Scheme.{w}) (x : X) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    ∃ e : S.obj (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r := by
  let D := (TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf
  let A := forget₂ CommRingCat.{w} RingCat.{w} ⋙
    forget₂ RingCat.{w} AddCommGrpCat.{w}
  let e : ↑(TopCat.Presheaf.stalk (C := Ab.{w})
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf x) ≃+ X.presheaf.stalk x :=
    (preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
  have hg (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
      e (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r := by
    change (colimit.ι (D ⋙ A) (Opposite.op (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) ≫
      (preservesColimitIso A D).inv) r = _
    rw [ι_preservesColimitIso_inv]
    rfl
  let f : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro r m
        obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hxV, m, rfl⟩ :=
          TopCat.Presheaf.exists_germ_eq
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf m
        have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
        rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
          ← TopCat.Presheaf.germ_res_apply
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf
            (homOfLE inf_le_right) x hx m,
          ← PresheafOfModules.germ_smul (R := X.presheaf)]
        let r' := X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r
        let m' : Γ(X, U ⊓ V) :=
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf.map
            (homOfLE inf_le_right : U ⊓ V ⟶ V).op m
        change e (TopCat.Presheaf.germ
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx (r' * m')) =
          X.presheaf.germ (U ⊓ V) x hx r' * (e (TopCat.Presheaf.germ
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx m') :
              X.presheaf.stalk x)
        rw [hg, hg]
        exact map_mul (X.presheaf.germ (U ⊓ V) x hx).hom _ _ }
  refine ⟨(LinearEquiv.ofBijective f e.bijective).toModuleIso, ?_⟩
  exact hg

/-- On a single stalk the range of ideal multiplication is the kernel of the pullback unit
(Stacks, Tags 08KS, 0098 and 00AE). -/
theorem closedImmersion_unit_stalk_kernel {Y Z : Scheme.{w}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (F : Y.Modules) (x : Y) :
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
    let J : Y.IdealSheafData := i.ker
    let μ : J.toModules ⊗ F ⟶ F := J.toModulesι ▷ F ≫ (λ_ F).hom
    let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace x
    LinearMap.range (S.map μ).hom = LinearMap.ker (S.map (adj.unit.app F)).hom := by
  classical
  dsimp only
  let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace x
  obtain ⟨e, he⟩ := unit_stalk_iso Y x
  have hm := Scheme.stalk_tensor_multiplication_range i.ker.toModulesι F x e he
  have hI := closedImmersion_ideal_stalk_range i x e he
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hx
    rw [hm, hI.1 z rfl]
    exact (closedImmersion_unit_stalk_kernel_on_image i F z).symm
  · rw [hm, hI.2 hx, Submodule.top_smul]
    have hz := (closedImmersion_pushforward_stalks i i.isClosedEmbedding
      ((tensorPullback i).obj F)).1 x hx
    symm
    apply top_unique
    intro m _
    exact hz.elim _ _

end
end AlgebraicGeometry.Scheme.Modules
