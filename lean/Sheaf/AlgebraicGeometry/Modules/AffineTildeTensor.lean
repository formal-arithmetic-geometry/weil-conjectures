/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Tensor products of tilde modules on an affine scheme

Source: Stacks Project, Schemes, Tags 01I7 and 01I8(1), second proof
(blueprint: lem-weil-pbc-affine-tilde-tensor).
-/

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

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
  sorry

end AlgebraicGeometry
