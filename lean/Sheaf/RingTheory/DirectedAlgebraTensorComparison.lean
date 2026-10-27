module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Directed algebra tensor comparison

Source: Stacks Project, Tag 0APJ, proof of lemma-affine-base-change, final assembly
using equation-sections-of-intersection; algebraic formulation with Tags 00D6,
00DA, 00DD and 01I4. (blueprint: lem-a1-directed-algebra-tensor-comparison)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace Algebra.TensorProduct

/-- Elementwise directed algebra presentations assemble compatible tensor isomorphisms.

Source: Stacks Project, Tag 0APJ, proof of lemma-affine-base-change, final sentence.
(blueprint: lem-a1-directed-algebra-tensor-comparison)

Proof:
1. The nonempty directed preorder is filtered. Forget the algebra diagrams and
   cocones to R-modules. The T-algebra structures and the scalar-tower and
   T-compatibility equations make the second diagram precisely its restriction
   of scalars along R → T. Exhaustion and eventual equality are the hypotheses of
   lem-weil-pbc-filtered-colimit-modules-criterion (Tags 00D6 and 00DA).
2. Apply that criterion to both cocones to obtain their module colimit properties.
3. Tensor the first colimit with T using lem-weil-pbc-tensor-commutes-with-colimits
   (Tag 00DD). Its legs are rho_i tensor 1 and its maps are a_ij tensor 1.
4. On pure tensors, T-linearity and compatibility of p_i with transitions show
   phi_j (a_ij tensor 1) = b_ij phi_i. Invert the stage isomorphisms to get the
   inverse compatibility. The two colimit properties induce linear maps Phi and
   Psi with Phi (rho_i tensor 1) = sigma_i phi_i and
   Psi sigma_i = (rho_i tensor 1) phi_i inverse.
5. Compute both composites on the cocone legs. Colimit uniqueness gives
   Psi Phi = 1 and Phi Psi = 1, and also uniqueness of the compatible linear iso.
6. By lem-weil-pbc-algebra-tensor-pushout-universal-property (Tag 01I4), the
   algebra tensor universal property gives h(c tensor t) = p(c) times t. Its
   composites with rho_i tensor 1 are sigma_i phi_i, hence h = Phi. The formula
   on 1 tensor t makes it a T-algebra map for the right-factor structure.
   Its linear inverse preserves multiplication, unit and T-scalars by applying
   the injective h to those identities. Thus Phi is the asserted T-algebra iso.
-/
theorem directedAlgebraTensorComparison
    (R T : Type u) [CommRing R] [CommRing T] [Algebra R T]
    (J : Type u) [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (A B : J ⥤ CommAlgCat.{u} R) (C : Cocone A) (D : Cocone B)
    [∀ i : J, Algebra T (B.obj i)] [∀ i : J, IsScalarTower R T (B.obj i)]
    [Algebra T D.pt] [IsScalarTower R T D.pt]
    (b_T : ∀ (i j : J) (f : i ⟶ j) (t : T),
      (B.map f).hom (algebraMap T (B.obj i) t) = algebraMap T (B.obj j) t)
    (sigma_T : ∀ (i : J) (t : T),
      (D.ι.app i).hom (algebraMap T (B.obj i) t) = algebraMap T D.pt t)
    (hC_surj : ∀ c : C.pt, ∃ (i : J) (x : A.obj i), (C.ι.app i).hom x = c)
    (hC_eq : ∀ (i : J) (x y : A.obj i), (C.ι.app i).hom x = (C.ι.app i).hom y →
      ∃ (j : J) (h : i ≤ j), (A.map (homOfLE h)).hom x = (A.map (homOfLE h)).hom y)
    (hD_surj : ∀ d : D.pt, ∃ (i : J) (x : B.obj i), (D.ι.app i).hom x = d)
    (hD_eq : ∀ (i : J) (x y : B.obj i), (D.ι.app i).hom x = (D.ι.app i).hom y →
      ∃ (j : J) (h : i ≤ j), (B.map (homOfLE h)).hom x = (B.map (homOfLE h)).hom y)
    (p : C.pt →ₐ[R] D.pt) (p_stage : ∀ i : J, A.obj i →ₐ[R] B.obj i)
    (hp : ∀ i : J, p.comp (C.ι.app i).hom = (D.ι.app i).hom.comp (p_stage i))
    (hp_stage : ∀ (i j : J) (f : i ⟶ j),
      (B.map f).hom.comp (p_stage i) = (p_stage j).comp (A.map f).hom)
    (hphi : ∀ i : J, Function.Bijective
      (productMap (p_stage i) (IsScalarTower.toAlgHom R T (B.obj i)))) :
    Nonempty (IsColimit
      ((forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙
        forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)).mapCocone C)) ∧
    Nonempty (IsColimit
      ((forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙
        forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)).mapCocone D)) ∧
    Nonempty (IsColimit
      ((forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙
        forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ⋙
        tensorRight (ModuleCat.of R T)).mapCocone C)) ∧
    ∃ Φ : C.pt ⊗[R] T ≃ₗ[R] D.pt,
      (∀ i : J, Φ.toLinearMap.comp ((C.ι.app i).hom.toLinearMap.rTensor T) =
        (D.ι.app i).hom.toLinearMap.comp
          (productMap (p_stage i) (IsScalarTower.toAlgHom R T (B.obj i))).toLinearMap) ∧
      (∀ Ψ : C.pt ⊗[R] T ≃ₗ[R] D.pt,
        (∀ i : J, Ψ.toLinearMap.comp ((C.ι.app i).hom.toLinearMap.rTensor T) =
          (D.ι.app i).hom.toLinearMap.comp
            (productMap (p_stage i) (IsScalarTower.toAlgHom R T (B.obj i))).toLinearMap) →
        Ψ = Φ) ∧
      ∃ e : @AlgEquiv T (C.pt ⊗[R] T) D.pt _ _ _
        (rightAlgebra (R := R) (A := C.pt) (B := T)) _,
        (∀ z : C.pt ⊗[R] T, e z = Φ z) ∧
        ∀ (c : C.pt) (t : T), e (c ⊗ₜ[R] t) = p c * algebraMap T D.pt t := by
  classical
  let U := forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙
    forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)
  let c := U.mapCocone C
  let d := U.mapCocone D
  have hc : IsColimit c := by
    apply isColimitOfReflects (forget (ModuleCat.{u} R))
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      obtain ⟨i, y, hy⟩ := hC_surj x
      exact ⟨i, y, hy.symm⟩
    · intro i x y h
      obtain ⟨j, hle, hj⟩ := hC_eq i x y h
      exact ⟨j, homOfLE hle, hj⟩
  have hd : IsColimit d := by
    apply isColimitOfReflects (forget (ModuleCat.{u} R))
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      obtain ⟨i, y, hy⟩ := hD_surj x
      exact ⟨i, y, hy.symm⟩
    · intro i x y h
      obtain ⟨j, hle, hj⟩ := hD_eq i x y h
      exact ⟨j, homOfLE hle, hj⟩
  let ct := (tensorRight (ModuleCat.of R T)).mapCocone c
  have hct : IsColimit ct := isColimitOfPreserves _ hc
  let phi (i : J) := productMap (p_stage i) (IsScalarTower.toAlgHom R T (B.obj i))
  let eStage (i : J) := (AlgEquiv.ofBijective (phi i) (hphi i)).toLinearEquiv
  let w : (A ⋙ U ⋙ tensorRight (ModuleCat.of R T)) ≅ B ⋙ U :=
    NatIso.ofComponents (fun i ↦ (eStage i).toModuleIso) (by
      intro i j f
      apply ModuleCat.hom_ext
      apply _root_.TensorProduct.ext'
      intro x t
      change p_stage j ((A.map f).hom x) * algebraMap T (B.obj j) t =
        (B.map f).hom (p_stage i x * algebraMap T (B.obj i) t)
      rw [map_mul, b_T]
      exact congrArg (fun y ↦ y * algebraMap T (B.obj j) t)
        (AlgHom.congr_fun (hp_stage i j f) x).symm)
  let eMod := hct.coconePointsIsoOfNatIso hd w
  let Phi : C.pt ⊗[R] T ≃ₗ[R] D.pt := eMod.toLinearEquiv
  have hPhi (i : J) : Phi.toLinearMap.comp
      ((C.ι.app i).hom.toLinearMap.rTensor T) =
      (D.ι.app i).hom.toLinearMap.comp (phi i).toLinearMap := by
    exact congrArg ModuleCat.Hom.hom (hct.comp_coconePointsIsoOfNatIso_hom hd w i)
  refine ⟨⟨hc⟩, ⟨hd⟩, ⟨hct⟩, Phi, hPhi, ?_, ?_⟩
  · intro Psi hPsi
    apply LinearEquiv.toLinearMap_injective
    apply congrArg ModuleCat.Hom.hom (hct.hom_ext
      (f := ModuleCat.ofHom Psi.toLinearMap) (f' := ModuleCat.ofHom Phi.toLinearMap) ?_)
    intro i
    exact ModuleCat.hom_ext ((hPsi i).trans (hPhi i).symm)
  · let h : C.pt ⊗[R] T →ₐ[R] D.pt :=
      productMap p (IsScalarTower.toAlgHom R T D.pt)
    have hh (i : J) : h.toLinearMap.comp
        ((C.ι.app i).hom.toLinearMap.rTensor T) =
        (D.ι.app i).hom.toLinearMap.comp (phi i).toLinearMap := by
      ext x t
      change p ((C.ι.app i).hom x) * algebraMap T D.pt t =
        (D.ι.app i).hom (p_stage i x * algebraMap T (B.obj i) t)
      rw [map_mul, sigma_T]
      exact congrArg (fun y ↦ y * algebraMap T D.pt t)
        (AlgHom.congr_fun (hp i) x)
    have heq : h.toLinearMap = Phi.toLinearMap := by
      apply congrArg ModuleCat.Hom.hom (hct.hom_ext
        (f := ModuleCat.ofHom h.toLinearMap) (f' := ModuleCat.ofHom Phi.toLinearMap) ?_)
      intro i
      exact ModuleCat.hom_ext ((hh i).trans (hPhi i).symm)
    let := rightAlgebra (R := R) (A := C.pt) (B := T)
    let hT : C.pt ⊗[R] T →ₐ[T] D.pt :=
      { h.toRingHom with
        commutes' := by
          intro t
          change h (1 ⊗ₜ[R] t) = algebraMap T D.pt t
          simp [h] }
    have hbij : Function.Bijective hT := by
      change Function.Bijective h
      have hfun : (h : C.pt ⊗[R] T → D.pt) = Phi :=
        funext (LinearMap.congr_fun heq)
      rw [hfun]
      exact Phi.bijective
    refine ⟨AlgEquiv.ofBijective hT hbij, ?_, ?_⟩
    · intro z
      exact LinearMap.congr_fun heq z
    · intro x t
      rfl

end Algebra.TensorProduct
