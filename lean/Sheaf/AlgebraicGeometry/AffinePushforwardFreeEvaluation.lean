/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Finite free evaluation over the direct-image algebra

Source: Stacks Project, Morphisms, Tag 01SB; Properties, Tag 01PB;
Cohomology of Schemes, Tag 0897, proof
(blueprint: lem-weil-pbc-affine-pushforward-free-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "AR" => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj A
set_option hygiene false in
local notation "PUSH" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := AR) (R := U.ringCatSheaf) (𝟙 AR)

/-- A finite free evaluation map into the algebra-valued direct image is epi on an
   affine open exactly when its map on sections over that open is surjective.
   Source: Stacks Project, Morphisms, Tag 01SB; Schemes, Tag 01IC
   (blueprint: lem-weil-pbc-affine-pushforward-free-evaluation).

Proof: Set W = f⁻¹ V and B = O_U(W). Both W and V are affine. The finite free
A|V-module is the direct image of O_W^I: finite coproducts are finite products,
and pushforward preserves products, compatibly with their basis sections.
The given sections define a map O_W^I → F|W. By the affine tilde-Gamma
correspondence, its image on W is the module image of B^I → F(W).
If the direct-image evaluation is epi, every section on V lifts locally.
Pulling the covering back to W puts its corresponding section in the sheaf
image on W, hence in the module image by the affine-sections image formula.
Conversely, surjectivity of B^I → F(W) makes O_W^I → F|W epi. On every affine
V' contained in V, W' = f⁻¹ V' is affine. Exactness of affine sections makes
O_U(W')^I → F(W') surjective. Thus the direct-image evaluation is surjective
on sections on an affine basis of V, so it is locally surjective and epi.
This uses only quasi-coherence of F and imposes no finite-type condition. -/
theorem affine_pushforward_free_evaluation [IsAffineHom f]
    (F : U.Modules) (hF : F.IsQuasicoherent) (V : X.Opens) (hV : IsAffineOpen V)
    (I : Type u) [Finite I]
    (s : I → (((PUSH).obj F).over V).sections) :
    Epi ((((PUSH).obj F).over V).freeHomEquiv.symm s) ↔
      Function.Surjective
        (((((PUSH).obj F).over V).freeHomEquiv.symm s).val.app (.op (Over.mk (𝟙 V)))) := by sorry

end AlgebraicGeometry.Scheme.Modules
