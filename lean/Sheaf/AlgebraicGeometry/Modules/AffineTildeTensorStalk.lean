/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-!
# The canonical affine tilde tensor comparison on stalks

Source: Stacks Project, Schemes, Tag 01I8(1), second proof.
(blueprint: lem-weil-pbc-affine-tilde-tensor-stalk-bijective)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison is bijective on each stalk.
Source: Stacks Project, Schemes, Tag 01I8(1), second proof, with Tags 01HV(7),
00DL and Modules 01CB.
(blueprint: lem-weil-pbc-affine-tilde-tensor-stalk-bijective)

Proof: Fix a prime p and let S be its complement. The stalk ring A is the
localization of R at S. The germ maps from M, N and M tensor_R N to their tilde
stalks are module localization maps at S (01HV(7)). Localization commutes with
tensor products (00DL), so m tensor n mapped to germ(m) tensor_A germ(n) is also
such a localization map. Identify the target stalk with the tensor of the two
stalks by 01CB. Naturality of germs and the assumed formula on global pure
tensors identify the composite of the stalk map with this localization map;
equality on all tensors follows by linearity and generation by pure tensors.
The resulting map between two localizations of the same module is bijective:
a target fraction lifts by its numerator and denominator, and a source fraction
in the kernel has numerator killed by an element of S and hence is zero.
Composing with the inverse of the stalk tensor identification proves the claim.
This also covers zero modules; for the zero ring there are no points to check. -/
theorem affine_tilde_tensor_stalk_bijective (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R)
    (α : tilde (ModuleCat.of R (M ⊗[R] N)) ⟶ tilde M ⊗ tilde N)
    (hα : ∀ (m : M) (n : N),
      α.val.app (op ⊤) (tilde.toOpen (ModuleCat.of R (M ⊗[R] N)) ⊤ (m ⊗ₜ[R] n)) =
        Scheme.Modules.tmulSection (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n))
    (x : Spec R) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      α.mapPresheaf) := by
  classical
  let A := (Spec R).presheaf.stalk x
  let S := x.asIdeal.primeCompl
  let Q := ModuleCat.of R (M ⊗[R] N)
  let LM := (tilde M).presheaf.stalk x
  let LN := (tilde N).presheaf.stalk x
  let LQ := (tilde Q).presheaf.stalk x
  let f := (tilde.toStalk M x).hom
  let g := (tilde.toStalk N x).hom
  let q := (tilde.toStalk Q x).hom
  let : IsLocalizedModule S q :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      Q x
  let : Algebra R A :=
    inferInstanceAs (Algebra R ((Spec.structureSheaf R).presheaf.stalk x))
  let : IsLocalization S A :=
    inferInstanceAs (IsLocalization.AtPrime ((Spec.structureSheaf R).presheaf.stalk x) x.asIdeal)
  let : IsScalarTower R A LM := .of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower R A LN := .of_algebraMap_smul fun _ _ ↦ rfl
  let t := (IsLocalization.moduleTensorEquiv S A LM LN).symm.restrictScalars R
  let v := t.toLinearMap ∘ₗ TensorProduct.map f g
  have hv : IsLocalizedModule S v := inferInstance
  obtain ⟨Φ, hΦ, _⟩ := SheafOfModules.stalkTensorIso (Spec R).toRingedSpace x
  let ψ : (tilde M ⊗ tilde N).presheaf.stalk x ≃ₗ[A] LM ⊗[A] LN :=
    (Φ (tilde M) (tilde N)).toLinearEquiv
  let h := ψ.toLinearMap ∘ₗ α.stalkLinearMap x
  let : IsScalarTower R A LQ := .of_algebraMap_smul fun _ _ ↦ rfl
  let hR := h.restrictScalars R
  have hcomm : hR ∘ₗ q = v := by
    ext m n
    change ψ (α.stalkLinearMap x (q (m ⊗ₜ[R] n))) = v (m ⊗ₜ[R] n)
    change ψ (α.stalkLinearMap x ((tilde Q).presheaf.germ ⊤ x (by simp)
      (tilde.toOpen Q ⊤ (m ⊗ₜ[R] n)))) = _
    rw [Scheme.Modules.Hom.stalkLinearMap_germ]
    change ψ ((tilde M ⊗ tilde N).presheaf.germ ⊤ x (by simp)
      (α.val.app (op ⊤) (tilde.toOpen Q ⊤ (m ⊗ₜ[R] n)))) = _
    rw [hα m n]
    exact hΦ (tilde M) (tilde N) ⊤ (by simp) (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n)
  have : IsLocalizedModule S (hR ∘ₗ q) := hcomm ▸ hv
  have hh : Function.Bijective hR := by
    rw [← IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp S q hR]
    exact (IsLocalizedModule.linearEquiv S q (hR ∘ₗ q)).bijective
  exact (Function.Bijective.of_comp_iff' ψ.bijective (α.stalkLinearMap x)).mp hh

end AlgebraicGeometry
