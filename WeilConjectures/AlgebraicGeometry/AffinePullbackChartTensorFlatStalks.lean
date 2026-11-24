/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffinePullbackChartTensorSections
import WeilConjectures.AlgebraicGeometry.AffineChartRelativeFlatCriterion
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Tensor flatness on one pulled-back affine chart

## References

* Stacks Project, Tags 01I4, 01IA, 01HV, 01U4 and 00HT
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

/-- On the inverse image of one affine open, flatness of the scalar-extended section
module is equivalent to relative flatness of the pulled-back stalks there.
There is no covering assumption and no flatness assertion outside this chart
(Stacks, Tags 01I4, 01IA, 01HV, 01U4 and 00HT). -/
theorem affine_pullback_chart_tensor_flat_iff_stalks
    (A T : CommRingCat.{u}) {X Y : Scheme.{u}} (f : X ⟶ Spec A)
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens)
    (q : A ⟶ T) (p : Y ⟶ Spec A) (e : Y ≅ Spec T)
    (he : e.hom ≫ Spec.map q = p) :
    (letI : Module (A : Type u) Γ(M, U.1) :=
      Module.compHom _ (((Scheme.ΓSpecIso A).inv ≫
        f.appLE ⊤ U.1 (by simp)).hom)
     letI : Algebra (A : Type u) (T : Type u) := q.hom.toAlgebra
     Module.Flat (T : Type u) ((T : Type u) ⊗[(A : Type u)] Γ(M, U.1))) ↔
    (∀ z : ↥(pullback f p : Scheme.{u}), (pullback.fst f p) z ∈ U.1 →
      Module.Flat (Y.presheaf.stalk ((pullback.snd f p) z))
        ((ModuleCat.restrictScalars ((pullback.snd f p).stalkMap z).hom).obj
          ((RingedSpace.moduleStalkFunctor (pullback f p).toRingedSpace z).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f p)).obj M)))) := by
  classical
  obtain ⟨W, hW, ⟨E⟩⟩ := exists_affine_pullback_chart_tensor_sections A T f M U q p e he
  let a := pullback.fst f p
  let b := pullback.snd f p
  let G := (Scheme.Modules.tensorPullback a).obj M
  let adj := (Scheme.Modules.nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction a)
  have : G.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pullback f p).ringCatSheaf).prop_of_iso
      (adj.app M).symm
      (inferInstanceAs (((Scheme.Modules.pullback a).obj M).IsQuasicoherent))
  have : IsAffine Y := (IsAffine.iff_of_isIso e.hom).mpr inferInstance
  let R := Γ(Y, ⊤)
  let N := Γ(G, W.1)
  let k : T ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso T).inv ≫ e.hom.appTop
  let : Algebra (T : Type u) R := k.hom.toAlgebra
  let : Module R N := Module.compHom _ (b.appLE ⊤ W.1 (by simp)).hom
  let : Module (T : Type u) N := Module.compHom _ k.hom
  have : IsScalarTower (T : Type u) R N := IsScalarTower.of_compHom _ _ _
  have : IsLocalization (⊥ : Submonoid (T : Type u)) R := by
    apply IsLocalization.of_le_isUnit_of_bijective
    · intro t ht
      obtain ⟨r, hr, rfl⟩ := ht
      have hr : r = 1 := by simpa using hr
      simp [hr]
    · exact ConcreteCategory.bijective_of_isIso k
  let : Module (A : Type u) Γ(M, U.1) :=
    Module.compHom _ (((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U.1 (by simp)).hom)
  let : Algebra (A : Type u) (T : Type u) := q.hom.toAlgebra
  have ht := Module.Flat.equiv_iff E
  have hr := Module.flat_iff_of_isLocalization R (⊥ : Submonoid (T : Type u)) N
  have hs := affine_chart_relative_flat_iff b G W
  refine ht.trans (hr.symm.trans (hs.trans ?_))
  apply forall_congr'
  intro z
  have hz : z ∈ W.1 ↔ a z ∈ U.1 := by rw [hW]; rfl
  exact imp_congr_left hz

end AlgebraicGeometry
