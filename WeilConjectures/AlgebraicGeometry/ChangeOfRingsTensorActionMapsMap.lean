/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
/-! # The presheaf change-of-rings map

Construction part of the tensor change-of-rings presentation.
-/

@[expose] public section

universe u
open CategoryTheory Opposite MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
/-- The presheaf change-of-rings map exists with its section formula.
Source: Stacks Project, Morphisms, proof of Lemma 01SB.
(blueprint: lem-weil-pbc-change-of-rings-tensor-action-maps-map).

Proof: on an open W send (c,p) to eta_W(c tensor_B p), where eta is
the change-of-rings sheafification unit. Additivity in each variable follows
from additivity of the pure tensor and linearity of eta. For a section r of
O_Y, the second-factor relation gives c tensor_B (B.hom(r)p) =
phi(B.hom(r))c tensor_B p = C.hom(r)c tensor_B p. Thus the pairing is
O_Y-balanced, and linear in either factor for the restricted O_Y-action on
the target. The sectionwise tensor universal property gives an O_Y-linear
map C(W) tensor_O P(W) to T(W). Restrictions send c tensor_B p to the tensor
of the restricted factors, and eta is natural; hence these maps commute
with restrictions on pure tensors. Tensor induction extends this equality
to every section. They therefore form the required presheaf morphism.
There is no sheafification extension in this lemma. Empty opens and zero
modules satisfy the same tensor universal properties.
-/
theorem exists_changeOfRings_tensor_presheaf_map (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
      (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
    letI := presheafMonoidalCategory Y
    ∃ (g : C.toModule.val ⊗ P₀.val ⟶ T.val),
      ∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        g.app (op W) (c ⊗ₜ[Y.presheaf.obj (op W)] p) =
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W))
            (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p) := by sorry
end AlgebraicGeometry.Scheme.Modules
