/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Sections of a tensor relation cokernel

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0089](https://stacks.math.columbia.edu/tag/0089)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- Module-level form: if `q` is a cokernel of `d`, where `d` imposes the `A`-balancing
relations on `M ⊗[R] N`, then `M ⊗[A] N` is additively isomorphic to `Q`, compatibly with
`q ∘ s`. -/
private theorem sectionQuotientAux
    {R A M N S F Q : Type u} [CommRing R] [CommRing A]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup S] [AddCommGroup F]
    [AddCommGroup Q] [Module R A] [Module R M] [Module R N] [Module R S]
    [Module R F] [Module R Q] [Module A M] [Module A N]
    (s : TensorProduct R M N →ₗ[R] S) (r : TensorProduct R A S →ₗ[R] F)
    (d : F →ₗ[R] S) (q : S →ₗ[R] Q)
    (hs : Function.Bijective s) (hr : Function.Surjective r)
    (hq : Function.Surjective q) (hk : q.ker = d.range)
    (ht : ∀ (a : R) (m : M) (n : N),
      (a • m) ⊗ₜ[A] n = m ⊗ₜ[A] (a • n))
    (hd : ∀ (a : A) (m : M) (n : N),
      d (r (a ⊗ₜ[R] s (m ⊗ₜ[R] n))) =
        s (m ⊗ₜ[R] (a • n)) - s ((a • m) ⊗ₜ[R] n)) :
    ∃ l : TensorProduct A M N ≃+ Q, ∀ (m : M) (n : N), l (m ⊗ₜ[A] n) = q (s (m ⊗ₜ[R] n)) := by
  let e := LinearEquiv.ofBijective s hs
  let t : M →+ N →+ TensorProduct A M N :=
    { toFun := fun m ↦
        { toFun := fun n ↦ m ⊗ₜ[A] n
          map_zero' := by simp
          map_add' := TensorProduct.tmul_add m }
      map_zero' := by ext n; simp
      map_add' := by intro m m'; ext n; exact TensorProduct.add_tmul m m' n }
  let f₀ := TensorProduct.liftAddHom t ht
  let f : S →+ TensorProduct A M N := f₀.comp e.symm.toAddMonoidHom
  have hf (m : M) (n : N) : f (s (m ⊗ₜ[R] n)) = m ⊗ₜ[A] n := by
    change f₀ (e.symm (e (m ⊗ₜ[R] n))) = _
    rw [e.symm_apply_apply]
    rfl
  have hqd (x : F) : q (d x) = 0 := by
    have hx : d x ∈ d.range := ⟨x, rfl⟩
    rw [← hk] at hx
    exact hx
  let a : M →+ N →+ Q :=
    { toFun := fun m ↦
        { toFun := fun n ↦ q (s (m ⊗ₜ[R] n))
          map_zero' := by simp
          map_add' := by intro n n'; simp [TensorProduct.tmul_add] }
      map_zero' := by ext n; simp
      map_add' := by intro m m'; ext n; simp [TensorProduct.add_tmul] }
  have ha (b : A) (m : M) (n : N) : a (b • m) n = a m (b • n) := by
    have h := hqd (r (b ⊗ₜ[R] s (m ⊗ₜ[R] n)))
    rw [hd, map_sub, sub_eq_zero] at h
    exact h.symm
  let g : TensorProduct A M N →+ Q := TensorProduct.liftAddHom a ha
  have hg (m : M) (n : N) : g (m ⊗ₜ[A] n) = q (s (m ⊗ₜ[R] n)) := rfl
  have hfd (x : F) : f (d x) = 0 := by
    obtain ⟨z, rfl⟩ := hr x
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul b v =>
      obtain ⟨z, rfl⟩ := hs.2 v
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]
      | tmul m n => rw [hd, map_sub, hf, hf, TensorProduct.smul_tmul, sub_self]
  have hker : q.toAddMonoidHom.ker ≤ f.ker := by
    intro x hx
    have hx' : x ∈ q.ker := hx
    rw [hk] at hx'
    obtain ⟨z, rfl⟩ := hx'
    exact hfd z
  let v : Q →+ TensorProduct A M N := q.toAddMonoidHom.liftOfSurjective hq ⟨f, hker⟩
  have hv (x : S) : v (q x) = f x :=
    AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hleft (x : TensorProduct A M N) : v (g x) = x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul m n => rw [hg, hv, hf]
  have hright (y : Q) : g (v y) = y := by
    obtain ⟨x, rfl⟩ := hq y
    rw [hv]
    obtain ⟨z, rfl⟩ := hs.2 x
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul m n => rw [hf, hg]
  exact ⟨{ g with invFun := v, left_inv := hleft, right_inv := hright }, hg⟩

set_option backward.isDefEq.respectTransparency false in
/-- A section cokernel of the balancing relation is the tensor product over B.
-/
theorem tensor_relation_section_quotient (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right))
    (δ : tensorObj B.toModule
      (tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) ⟶
      tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P))
    (W : Y.Opens)
    (hrel : ∀ (b : B.right.obj.obj (op W)) (c : C.right.obj.obj (op W))
        (p : P.val.obj (op W)),
      δ.app W (tmulSection (M := B.toModule) b
        (tmulSection (M := C.toModule)
          (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
        tmulSection (M := C.toModule)
          (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c (b • p) -
        tmulSection (M := C.toModule)
          (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)
            (φ.right.hom.app (op W) b * c) p)
    (hS : Function.Bijective (tensorSectionsMap C.toModule
      ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) W))
    (hF : Function.Bijective (tensorSectionsMap B.toModule
      (tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) W))
    (hq : Function.Surjective ((cokernel.π δ).app W))
    (hk : LinearMap.ker ((cokernel.π δ).val.app (op W)).hom =
      LinearMap.range (δ.val.app (op W)).hom) :
    ∃ l : (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P).obj (op W) ≃+
        Γ(cokernel δ, W),
      ∀ (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        l (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p) =
          (cokernel.π δ).app W (tmulSection (M := C.toModule)
            (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p) := by
  let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
  let : Module (B.right.obj.obj (op W)) (C.right.obj.obj (op W)) :=
    Module.compHom _ (φ.right.hom.app (op W)).hom
  let : Module Γ(Y, W) (B.right.obj.obj (op W)) :=
    Module.compHom _ (B.hom.hom.app (op W)).hom
  let : Module Γ(Y, W) (C.right.obj.obj (op W)) :=
    Module.compHom _ (C.hom.hom.app (op W)).hom
  let : Module Γ(Y, W) (P.val.obj (op W)) :=
    Module.compHom _ (B.hom.hom.app (op W)).hom
  have hstruct (r : Γ(Y, W)) :
      φ.right.hom.app (op W) (B.hom.hom.app (op W) r) = C.hom.hom.app (op W) r := by
    exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app (op W)) φ.w) r
  apply sectionQuotientAux (A := B.right.obj.obj (op W))
    (M := C.right.obj.obj (op W)) (N := P.val.obj (op W))
    (tensorSectionsMap C.toModule P₀ W)
    (tensorSectionsMap B.toModule (tensorObj C.toModule P₀) W)
    (δ.val.app (op W)).hom ((cokernel.π δ).val.app (op W)).hom
    hS hF.2 hq hk
  · intro r c p
    change (C.hom.hom.app (op W) r * c) ⊗ₜ[B.right.obj.obj (op W),
      (φ.right.hom.app (op W)).hom] p =
      c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom]
        ((B.hom.hom.app (op W) r) • p)
    rw [← hstruct r]
    exact TensorProduct.smul_tmul (R := B.right.obj.obj (op W))
      (B.hom.hom.app (op W) r) c p
  · exact hrel

end AlgebraicGeometry.Scheme.Modules
