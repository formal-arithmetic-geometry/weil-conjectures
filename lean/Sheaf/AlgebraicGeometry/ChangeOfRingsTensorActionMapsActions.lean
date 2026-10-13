/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
/-! # The two tensor action maps

Construction part of the tensor change-of-rings presentation.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
/-- The two action maps exist with their section formulas.
Source: Stacks Project, Morphisms, proof of Lemma 01SB.
(blueprint: lem-weil-pbc-change-of-rings-tensor-action-maps-actions).

Proof: put P₀ = P restricted to O_Y and K = C.toModule.val tensor P₀.val.
Give K the two B-actions b(c tensor p) = c tensor bp and
b(c tensor p) = phi(b)c tensor p. The first respects O_Y-balancing by
commutativity of B and the scalar-tower identity; the second respects it
because phi is an O_Y-algebra morphism. Restrictions commute with each
action by naturality of phi and semilinearity of the module restrictions.
Sheafify each B-module presheaf. After restriction to O_Y both associated
module sheaves identify with the O_Y-sheafification of K: the underlying
additive sheafification is the same and the O_Y-action is uniquely determined
by its restriction to the sheafification unit. Transport the B-actions
through these identifications to S = C.toModule tensor P₀. Their pairings
B.toModule.val times S.val are O_Y-bilinear and natural. Apply the sectionwise
tensor universal property and then the sheafification adjunction to obtain
a and d. The identifications preserve the units, so on the indicated double
pure tensors their values are c tensor bp and phi(b)c tensor p. The universal
properties apply to empty opens and zero modules without extra hypotheses.
-/
theorem exists_changeOfRings_tensor_action_maps_actions (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    ∃ (a d : tensorObj B.toModule (tensorObj C.toModule
      ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) ⟶
      tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)),
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
        (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        a.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule)
            (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
          tmulSection (M := C.toModule)
            (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c (b • p)) ∧
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
        (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        d.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule)
            (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
          tmulSection (M := C.toModule)
            (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)
            (φ.right.hom.app (op W) b * c) p) := by sorry
end AlgebraicGeometry.Scheme.Modules
