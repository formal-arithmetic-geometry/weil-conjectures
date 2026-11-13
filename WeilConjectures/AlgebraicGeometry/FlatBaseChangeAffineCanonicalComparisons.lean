/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import WeilConjectures.AlgebraicGeometry.AffineCohomologySectionEquiv
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeTargetLerayComparison

/-! # Canonical affine section comparisons before flat base change

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

set_option maxHeartbeats 800000 in
-- Explicit homology transports need more elaboration than the default budget.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical source and target affine comparisons, compatible with the cohomological
pullback. This asserts no invertibility of the cohomological base-change map and needs
no flatness of either projection. (Stacks, Tags 02KH, 01XJ, 01XK, 01E4 and 03FD.) -/
theorem Scheme.Modules.exists_flatBaseChange_affine_canonical_comparisons
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (I : InjectiveResolution F)
    (J : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F))
    (p : ℕ) (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f g F I J V) :
    letI : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F
    let P := ((Scheme.Modules.pushforward f).rightDerived p).obj F
    let Q := ((Scheme.Modules.pushforward (pullback.fst g f)).rightDerived p).obj
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F)
    ∃ (e0 : ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+
          Scheme.Modules.HOver h N p)
      (a0 : TensorProduct Γ(S, V) Γ(S', W) (Scheme.Modules.HOver h N p) ≃ₗ[Γ(S', W)]
        Γ((Scheme.Modules.tensorPullback g).obj P, W))
      (b0 : Scheme.Modules.HOver (Scheme.Modules.baseChangeSnd (S := Γ(S', W)) h)
          (Scheme.Modules.baseChangedModule (S := Γ(S', W)) h N) p ≃ₗ[Γ(S', W)]
          Γ(Q, W)),
      (∀ (s : Γ(S', W)) (xi : Scheme.Modules.HOver h N p),
        a0 (s ⊗ₜ[Γ(S, V)] xi) = s •
          ((Scheme.Modules.tensorPullback g).obj P).presheaf.map (homOfLE eVW).op
            (Scheme.Modules.Hom.app
              ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app P)
              V (D.sourceClass p (e0.symm xi)))) ∧
      (∀ xi : Scheme.Modules.HOver h N p,
        b0 (Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p xi) =
          Q.presheaf.map (homOfLE eVW).op
            (D.targetClass p
              (Scheme.Modules.moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
                ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p (e0.symm xi)))) := by
  classical
  dsimp only
  let : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
  let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
  let N := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F
  let P := ((Scheme.Modules.pushforward f).rightDerived p).obj F
  let : ∀ G : S.Modules, Module Γ(S, V)
      Γ((Scheme.Modules.tensorPullback g).obj G, W) :=
    fun G ↦ Module.compHom _ (g.appLE V W eVW).hom
  obtain ⟨c, hc, hs, ht, _⟩ :=
    Scheme.Modules.exists_tensorPullback_affine_sections g ⟨V, hV⟩ ⟨W, hW⟩ eVW
  have target :=
    Scheme.Modules.exists_flatBaseChange_target_leray_comparison
      f g F I J p V W hV hW eVW D
  obtain ⟨E, hE, htarget⟩ := target
  obtain ⟨eH, heH, b0, hb0⟩ := htarget
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have edge :=
    Scheme.Modules.exists_affine_cohomology_section_equiv f F I p V hV D.source E hE
  obtain ⟨e, he⟩ := edge
  have hP : P.IsQuasicoherent := by
    exact ordinaryHigherImage_isQuasicoherent f F inferInstance p
  let k : (Γ(S', W) ⊗[Γ(S, V)] Γ(P, V)) →ₗ[Γ(S', W)]
      Γ((Scheme.Modules.tensorPullback g).obj P, W) :=
    { toFun := fun t ↦ c P hP ((TensorProduct.comm Γ(S, V) Γ(P, V) Γ(S', W)).symm t)
      map_add' := by intro t t'; simp
      map_smul' := by
        intro b t
        simpa only [LinearEquiv.apply_symm_apply, RingHom.id_apply] using
          hs P hP b ((TensorProduct.comm Γ(S, V) Γ(P, V) Γ(S', W)).symm t) }
  let t : (Γ(S', W) ⊗[Γ(S, V)] Scheme.Modules.HOver h N p) ≃ₗ[Γ(S', W)]
      (Γ(S', W) ⊗[Γ(S, V)] Γ(P, V)) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Γ(S', W) Γ(S', W)) e
  have hk : Function.Bijective (k.comp t.toLinearMap) :=
    (hc P hP).comp
      ((TensorProduct.comm Γ(S, V) Γ(P, V) Γ(S', W)).symm.bijective.comp t.bijective)
  refine ⟨eH, LinearEquiv.ofBijective (k.comp t.toLinearMap) hk, b0, ?_, ?_⟩
  · intro s xi
    change c P hP (e xi ⊗ₜ[Γ(S, V)] s) = _
    have he' : e xi = D.sourceClass p (eH.symm xi) := by
      rw [heH]
      exact he xi
    exact (ht P hP (e xi) s).trans (congrArg (fun z ↦ s •
      ((Scheme.Modules.tensorPullback g).obj P).presheaf.map (homOfLE eVW).op
        (Scheme.Modules.Hom.app
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app P)
          V z)) he')
  · dsimp only at hb0
    exact hb0
end AlgebraicGeometry
