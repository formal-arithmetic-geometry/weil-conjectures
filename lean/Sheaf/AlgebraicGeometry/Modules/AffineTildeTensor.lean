/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.Modules.AffineTildeTensorStalk

/-!
# Tensor products of tilde modules on an affine scheme

Source: Stacks Project, Schemes, Tags 01I7 and 01I8(1), second proof
(blueprint: lem-weil-pbc-affine-tilde-tensor).
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The canonical global tensor map is linear and bijective, and extends uniquely to an
isomorphism of sheaves. Source: Stacks Project, Schemes, Tags 01I7 and 01I8(1)
(blueprint: lem-weil-pbc-affine-tilde-tensor).

Proof:
The tensor `tilde M ⊗ tilde N` is that of `SheafOfModules.monoidalCategory` on
`(Spec R).Modules`, the sheafification of the presheaf tensor product
(`SheafOfModules.tensorObjIsoSheafification`); `Scheme.Modules.tmulSection a b` is the image
of `a ⊗ b` under the sheafification map.
1. The maps `tilde.toOpen` are R-linear (lem-weil-pbc-spec-module-tilde-sections).
Their tensor followed by the sheafification map (`tmulSection`) is bilinear, hence defines
beta by the module tensor universal property (def-pur-sheaf-tensor-product and
 def-weil-presheaf-modules-sheafification).
2. The tilde-global-sections adjunction (lem-weil-pbc-affine-tilde-gamma-adjunction)
extends beta uniquely to alpha; pure tensors generate, giving the displayed formula.
3. At a prime, the ring stalk and the three tilde stalks are localizations
(lem-weil-pbc-spec-domain-stalks-function-field, def-weil-pbc-module-stalk and
lem-weil-pbc-spec-tilde-stalk-localization). Tensor commutes with localization
(lem-weil-pbc-localization-tensor-product).
4. The stalk tensor comparison (lem-weil-pbc-module-stalk-tensor) identifies alpha on
germs of pure global tensors with the tensor localization map.
5. Both source and target are localizations of the same module. Every element is a fraction;
surjectivity follows by lifting its numerator. A fraction in the kernel has a numerator
annihilated by a denominator, so is zero. Thus every stalk map is bijective.
6. The stalk criterion (lem-weil-pbc-module-iso-on-stalks) makes alpha an isomorphism.
7. The tilde unit on global sections is bijective
(lem-weil-pbc-affine-tilde-gamma-adjunction); beta is its composite with alpha on global
sections and is therefore bijective. -/
theorem affine_tilde_tensor (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) :
    ∃ β : M ⊗[R] N →ₗ[R] Γ(tilde M ⊗ tilde N, ⊤),
      (∀ (m : M) (n : N), β (m ⊗ₜ[R] n) =
        Scheme.Modules.tmulSection (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n)) ∧
      Function.Bijective β ∧
      ∃ α : tilde (ModuleCat.of R (M ⊗[R] N)) ⟶ tilde M ⊗ tilde N,
        (∀ z : M ⊗[R] N,
          α.val.app (op ⊤) (tilde.toOpen (ModuleCat.of R (M ⊗[R] N)) ⊤ z) = β z) ∧
        IsIso α ∧
        ∀ α' : tilde (ModuleCat.of R (M ⊗[R] N)) ⟶ tilde M ⊗ tilde N,
          (∀ z : M ⊗[R] N,
            α'.val.app (op ⊤) (tilde.toOpen (ModuleCat.of R (M ⊗[R] N)) ⊤ z) = β z) →
          α' = α := by
  classical
  let b : M →ₗ[R] N →ₗ[R] Γ(tilde M ⊗ tilde N, ⊤) :=
    { toFun := fun m ↦
        { toFun := fun n ↦ Scheme.Modules.tmulSection
            (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n)
          map_add' := fun n n' ↦ by
            rw [map_add, Scheme.Modules.tmulSection_add]
          map_smul' := fun r n ↦ by
            rw [map_smul]
            simp only [RingHom.id_apply, Scheme.Modules.smul_Spec_def]
            exact Scheme.Modules.tmulSection_smul _ _ _ }
      map_add' := fun m m' ↦ by
        ext n
        dsimp
        rw [map_add, Scheme.Modules.add_tmulSection]
      map_smul' := fun r m ↦ by
        ext n
        dsimp
        rw [map_smul]
        simp only [Scheme.Modules.smul_Spec_def]
        exact Scheme.Modules.smul_tmulSection _ _ _ }
  let β := TensorProduct.lift b
  have hβ (m : M) (n : N) : β (m ⊗ₜ[R] n) =
      Scheme.Modules.tmulSection (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n) := rfl
  let Q := ModuleCat.of R (M ⊗[R] N)
  let F := tilde M ⊗ tilde N
  let e := (tilde.adjunction (R := R)).homEquiv Q F
  let βhom : Q ⟶ (moduleSpecΓFunctor (R := R)).obj F := ConcreteCategory.ofHom β
  let α := e.symm βhom
  have hα (z : M ⊗[R] N) :
      α.val.app (op ⊤) (tilde.toOpen Q ⊤ z) = β z := by
    have h := congrArg ModuleCat.Hom.hom (e.apply_symm_apply βhom)
    change (e α).hom z = βhom.hom z
    exact DFunLike.congr_fun h z
  have huniq (α' : tilde Q ⟶ F)
      (h : ∀ z, α'.val.app (op ⊤) (tilde.toOpen Q ⊤ z) = β z) : α' = α := by
    apply e.injective
    rw [show e α = βhom from e.apply_symm_apply βhom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact h z
  have hstalk (x : Spec R) :
      Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        α.mapPresheaf) :=
    affine_tilde_tensor_stalk_bijective R M N α (fun m n ↦ (hα _).trans (hβ m n)) x
  have hiso : IsIso α := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
      (F := ⟨(tilde Q).presheaf, (tilde Q).isSheaf⟩)
      (G := ⟨F.presheaf, F.isSheaf⟩) ⟨α.mapPresheaf⟩ U fun x _ ↦ hstalk x
  have hbij : Function.Bijective β := by
    have hu := ConcreteCategory.bijective_of_isIso (tilde.toOpen Q ⊤)
    have ha := ConcreteCategory.bijective_of_isIso (α.app ⊤)
    have heq : (β : M ⊗[R] N → Γ(F, ⊤)) = (α.app ⊤) ∘ (tilde.toOpen Q ⊤) := by
      funext z
      exact (hα z).symm
    rw [heq]
    exact ha.comp hu
  exact ⟨β, hβ, hbij, α, hα, hiso, huniq⟩

end AlgebraicGeometry
