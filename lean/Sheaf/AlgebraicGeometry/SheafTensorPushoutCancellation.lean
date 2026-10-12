/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Cancellation of tensor extension over a pushout of ring sheaves

Source: Stacks Project, Tag 01SB, tensor construction, and Tag 008A.
(blueprint: lem-weil-pbc-sheaf-tensor-pushout-cancellation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ChangeOfRings

namespace SheafOfModules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : TopCat.{u}} {D C A B : T.Sheaf CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat.{u} RingCat.{u})).obj E
set_option hygiene false in
local notation "𝓻" a =>
  (sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat.{u} RingCat.{u})).map a
/-- Tensor cancellation across a pushout, naturally in the module, including its tensor unit.
Source: Stacks Project, Tag 01SB (tensor construction and elucidation), Tag 008A.
Proof: sheafify the presheaf of rings W ↦ C(W) tensor over D(W) with A(W).
A pair of maps out of C and A agreeing on D defines on each open the ring map
c tensor a ↦ u(c)v(a); these maps commute with restriction and uniquely extend through
sheafification. Thus this sheaf is a pushout, and its canonical map to B is an isomorphism.
Put L = sheafification of W ↦ C(W) tensor over D(W) with M(W). The formula
(c tensor a)(c' tensor m) = cc' tensor (a • m) defines the pushout-ring action on L:
balancing proves well-definedness before sheafification, local representatives extend it,
and uniqueness of sheaf gluing proves independence and all action laws.
The A-linear map m ↦ sheafification(1 tensor m) then extends B-linearly to
B tensor over A with M, by β tensor m ↦ β • sheafification(1 tensor m).
After restricting to C this is the forward comparison. Its inverse is the sheafification
of c tensor m ↦ b(c) tensor m; D-balancing follows from r followed by b = s followed by t.
The forward-inverse composite fixes c tensor m. For the other composite, locally write
β as a sum of c tensor a in the sheafified pushout. A-balancing gives
b(c)t(a) tensor m = b(c) tensor (a • m), so it fixes β tensor m locally, hence globally.
These formulas commute with every restriction and with each linear map M → N, proving
naturality. The inverse takes 1 tensor m to b(1) tensor m = 1 tensor m on every open.
All constructions use balanced tensor relations and sheaf gluing, with no flatness or
nonzero-ring assumption; the zero module and empty open are included.
(blueprint: lem-weil-pbc-sheaf-tensor-pushout-cancellation). -/
theorem sheafTensorPushoutCancellation
    (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (hp : IsPushout r s b t) :
    ∃ e : ∀ M : SheafOfModules.{u} (𝓡 A),
      (restrictScalars (𝓻 b)).obj (changeOfRings.{u, u, u} t M) ≅
        changeOfRings.{u, u, u} r ((restrictScalars (𝓻 s)).obj M),
      (∀ (M N : SheafOfModules.{u} (𝓡 A)) (a : M ⟶ N),
        (restrictScalars (𝓻 b)).map (changeOfRingsHom t M a) ≫ (e N).hom =
          (e M).hom ≫ changeOfRingsHom r ((restrictScalars (𝓻 s)).obj M)
            ((restrictScalars (𝓻 s)).map a)) ∧
      (∀ (M : SheafOfModules.{u} (𝓡 A)) (W : (Opens T)ᵒᵖ) (m : M.val.obj W),
        (e M).inv.val.app W
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C).obj)).unit.app
            (changeOfRingsPresheaf.{u, u, u} r ((restrictScalars (𝓻 s)).obj M))).app W
            ((1 : C.obj.obj W) ⊗ₜ[D.obj.obj W, (r.hom.app W).hom] m)) =
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} t M)).app W 
          ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m)) := by
  sorry

end
end SheafOfModules
