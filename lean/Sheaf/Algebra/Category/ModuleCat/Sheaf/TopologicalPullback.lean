/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Topology.InverseImageModule

/-!
# Inverse image of sheaf modules and direct image

Source: Stacks Project, Sheaves, Tags 008X and 008Y
(blueprint: lem-pc-module-inverse-image-adjunction).
The inverse-image module is the landed `TopCat.Sheaf.inverseImageModule`
(the 008X structure on the explicit abelian inverse image), not Mathlib's
abstract `SheafOfModules.pullback`.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopCat Opposite TopologicalSpace

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The abelian inverse-image/direct-image adjunction bijection restricts to a natural
bijection between linear morphisms `f⁻¹M ⟶ N` over `f⁻¹A` and linear morphisms
`M ⟶ f_* N` over `A`, where `A` acts on `f_* N` through the unit `η_A`.
Source: Stacks Project, Sheaves, Tags 008X and 008Y.
(blueprint: lem-pc-module-inverse-image-adjunction). -/
def moduleInverseImageAdjunctionSpec {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A : Y.Sheaf CommRingCat.{u}) : Prop :=
  let J := Opens.grothendieckTopology Y
  let K := Opens.grothendieckTopology X
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A
  let R' := (sheafCompose K (forget₂ CommRingCat RingCat)).obj
    (TopCat.Sheaf.inverseImageRing f A)
  let η : R ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} J K).obj R' :=
    (sheafCompose J (forget₂ CommRingCat RingCat)).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) CommRingCat.{u} J K).unit.app A)
  let adjAb := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) AddCommGrpCat.{u} J K
  ∃ φ : ∀ (M : SheafOfModules.{u} R) (N : SheafOfModules.{u} R'),
      (TopCat.Sheaf.inverseImageModule f A M ⟶ N) ≃
        (M ⟶ (SheafOfModules.pushforward.{u} η).obj N),
    (∀ (M : SheafOfModules.{u} R) (N : SheafOfModules.{u} R')
        (ψ : TopCat.Sheaf.inverseImageModule f A M ⟶ N) (V : (Opens Y)ᵒᵖ)
        (x : M.val.obj V),
      ((φ M N ψ).val.app V).hom x =
        (ψ.val.app ((Opens.map f).op.obj V)).hom
          ((adjAb.unit.app ((SheafOfModules.toSheaf R).obj M)).hom.app V x)) ∧
    (∀ (M M' : SheafOfModules.{u} R) (N : SheafOfModules.{u} R') (a : M' ⟶ M)
        (ψ : TopCat.Sheaf.inverseImageModule f A M ⟶ N),
      φ M' N (TopCat.Sheaf.inverseImageModuleMap f A M' a ≫ ψ) = a ≫ φ M N ψ) ∧
    (∀ (M : SheafOfModules.{u} R) (N N' : SheafOfModules.{u} R')
        (ψ : TopCat.Sheaf.inverseImageModule f A M ⟶ N) (b : N ⟶ N'),
      φ M N' (ψ ≫ b) = φ M N ψ ≫ (SheafOfModules.pushforward.{u} η).map b)

/-- The inverse-image module adjunction: the abelian adjunction restricts to linear maps,
naturally in both modules. Source: Stacks Project, Sheaves, Tags 008X and 008Y.

Proof, following the four steps of the node:
1. Apply `lem-pc-presheaf-module-inverse-image-adjunction` (1) to `A` and `M`.
Its coprojection formula defines the action on `f_p M`. Apply
`lem-pc-presheaf-module-sheafification-ring` to sheafify this module over `f_p A`.
The underlying abelian sheaf is `(f_p M)^#`, and the sheafification map is semilinear
for `theta_A`. Naturality gives linear maps on inverse images (008X).
2. Regard `N` as an `f_p A`-module through `theta_A`. The universal property in
`lem-pc-presheaf-module-sheafification-ring` identifies linear maps from `(f_p M)^#`
to `N` with linear presheaf maps from `f_p M` to `N`. On abelian maps this is
composition with `theta_M`, by `def-weil-pbc-sheafification`.
3. Apply `lem-pc-presheaf-module-inverse-image-adjunction` (3). The presheaf
adjunction sends a map `psi` to `f_* psi` composed with `i_M`. The scalar action on
its target is through `i_A` and then `theta_A`, hence through `eta_A`. Direct image
is a sheaf by `def-weil-pbc-topological-inverse-image` (1), and its module morphisms
are exactly its linear presheaf morphisms by `def-weil-sheaf-of-modules-category`.
4. Compose the two natural bijections. On abelian maps the composite sends `alpha`
to `f_* alpha` composed with `f_* theta_M` composed with `i_M`, which is
`f_* alpha` composed with `eta_M`, the abelian adjunction formula of
`def-weil-pbc-topological-inverse-image` (3). Thus it restricts the abelian
bijection exactly to linear maps and is natural in both modules.
(blueprint: lem-pc-module-inverse-image-adjunction). -/
theorem moduleInverseImageAdjunction {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A : Y.Sheaf CommRingCat.{u}) : moduleInverseImageAdjunctionSpec f A := by
  sorry

end SheafOfModules
