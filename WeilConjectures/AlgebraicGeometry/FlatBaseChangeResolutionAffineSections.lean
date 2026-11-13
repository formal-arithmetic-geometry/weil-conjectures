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
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeAffineDictionary
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionSections
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoicesExist

/-! # Affine sections of the resolution-defined flat base-change comparison

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

set_option maxHeartbeats 500000 in
-- Comparing the resolution and tensor cohomology interfaces needs extra elaboration steps.
/-- On affine opens `W` and `V` with `g(W)` contained in `V`, bijectivity of the actual
resolution comparison is exactly bijectivity of the canonical scalar-extension
comparison for cohomology over the ring of sections of `V`.
(Stacks, Tags 02KH, 02N7, 01E4 and 03FD.) -/
theorem Scheme.Modules.flatBaseChangeResolutionBeta_affine_bijective_iff
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [Flat (pullback.snd g f)]
    (F : X.Modules) [F.IsQuasicoherent]
    (I : InjectiveResolution F)
    (J : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((Scheme.Modules.pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
        (pullback.snd g f))).unit.app F ≫
          (Scheme.Modules.pushforward (pullback.snd g f)).map (J.ι.f 0)) (p : ℕ)
    (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (e : W ≤ g ⁻¹ᵁ V) :
    letI : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W e).hom.toAlgebra
    Function.Bijective
      (Scheme.Modules.Hom.app (Scheme.Modules.flatBaseChangeResolutionBeta f g I J t p) W) ↔
      Function.Bijective (Scheme.Modules.H.baseChange (S := Γ(S', W))
        (f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ)
        ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F) p) := by
  classical
  let : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W e).hom.toAlgebra
  let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
  let N := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F
  let β := Scheme.Modules.flatBaseChangeResolutionBeta f g I J t p
  obtain ⟨D⟩ := Scheme.Modules.flatBaseChangeMap_sections_choices f g F I J V
  obtain ⟨eH, a, b, ha, hb, ha_tmul, hb_pullback⟩ :=
    Scheme.Modules.exists_flatBaseChange_affine_dictionary f g F I J p V W hV hW e D
  have hcomm (z : TensorProduct Γ(S, V) Γ(S', W) (Scheme.Modules.HOver h N p)) :
      Scheme.Modules.Hom.app β W (a z) =
        b (Scheme.Modules.H.baseChange (S := Γ(S', W)) h N p z) := by
    induction z using TensorProduct.inductionOn with
    | tmul s xi =>
      rw [ha_tmul, Scheme.Modules.Hom.app_smul]
      have hs := Scheme.Modules.flatBaseChangeResolutionBeta_sections f g I J t ht p
        V D (eH.symm xi)
      rw [Adjunction.homEquiv_unit] at hs
      change Scheme.Modules.Hom.app β (g ⁻¹ᵁ V)
        (Scheme.Modules.Hom.app
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
            (((Scheme.Modules.pushforward f).rightDerived p).obj F)) V
          (D.sourceClass p (eH.symm xi))) = _ at hs
      have hn := β.val.naturality (homOfLE e).op
      have hn' := congrArg (fun q ↦ q
        (Scheme.Modules.Hom.app
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
            (((Scheme.Modules.pushforward f).rightDerived p).obj F)) V
          (D.sourceClass p (eH.symm xi)))) hn
      change _ = b (s • Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p xi)
      rw [b.map_smul, hb_pullback]
      congr 1
      exact hn'.trans (congrArg
        (fun z ↦ (((Scheme.Modules.pushforward (pullback.fst g f)).rightDerived p).obj
          ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F)).presheaf.map
            (homOfLE e).op z) hs)
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have hc : (Scheme.Modules.Hom.app β W : _ → _) ∘ a =
      b ∘ (Scheme.Modules.H.baseChange (S := Γ(S', W)) h N p) := funext hcomm
  constructor
  · intro hβ
    have H := (hβ.comp ha)
    rw [hc] at H
    exact (hb.of_comp_iff' _).mp H
  · intro hH
    have H := hb.comp hH
    rw [← hc] at H
    exact (Function.Bijective.of_comp_iff _ ha).mp H


end AlgebraicGeometry
