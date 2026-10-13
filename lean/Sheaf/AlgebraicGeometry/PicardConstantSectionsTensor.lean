/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Constant vector-space coefficients extended to the structure presheaf

Source: Stacks Project, Varieties, Tag 0BED, degree-zero tensor calculation.
The construction is extension of scalars of a constant presheaf, followed by
pointwise tensor with the coefficient presheaf. No choice of a basis enters it.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- The constant ring map induced by the structure morphism.
Source: Stacks Project, Varieties, Tag 0BED, scalar coefficients in the ordinary
pushforward tensor formula.
(blueprint: lem-sc-picard-constant-sections-tensor-basis). -/
def picardConstantRingMap (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) :
    (Functor.const Y.Opensᵒᵖ).obj (RingCat.of k) ⟶
      (𝟭 Y.Opens).op ⋙ Y.ringCatSheaf.obj where
  app U := RingCat.ofHom (scalarMap g U.unop)
  naturality U V i := by
    ext r
    change scalarMap g V.unop r = (Y.presheaf.map i).hom (scalarMap g U.unop r)
    simp only [scalarMap, RingHom.comp_apply]
    change _ = (Y.presheaf.map (homOfLE (le_top (a := U.unop))).op ≫
      Y.presheaf.map i) _
    rw [← Y.presheaf.map_comp]
    rfl

/-- The constant presheaf of vector spaces as modules over the constant ring.
Source: Stacks Project, Varieties, Tag 0BED, constant Gamma(X,F) coefficients.
(blueprint: lem-sc-picard-constant-sections-tensor-basis). -/
def picardConstantVector (k : Type w) [Field k] (Y : Scheme.{w}) (M : ModuleCat.{w} k) :
    _root_.PresheafOfModules ((Functor.const Y.Opensᵒᵖ).obj (RingCat.of k)) where
  obj _ := M
  map _ := ModuleCat.ofHom (LinearMap.id)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Extend the constant vector space to O_Y, then tensor it with G, pointwise.
Source: Stacks Project, Varieties, Tag 0BED, ordinary pushforward tensor coefficients.
(blueprint: lem-sc-picard-constant-sections-tensor-basis). -/
def picardConstantSectionsTensor (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules) :
    _root_.PresheafOfModules Y.ringCatSheaf.obj :=
  ((PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
    (picardConstantVector k Y M)) ⊗ G.val


/-- A prescribed basis identifies the tensor coefficient presheaf with a coproduct.
Source: Stacks Project, Varieties, Tag 0BED, the second isomorphism in the
ordinary direct-image calculation.
(blueprint: lem-sc-picard-constant-sections-tensor-basis).

Proof: The constant vector presheaf sends each open to M with identity restriction.
The basis identifies it with the coproduct of I copies of the constant k-module k:
on sections the map sends the i-th coefficient a to a times b_i, and the inverse
is b.repr. Constant-presheaf coproducts are pointwise, and these maps commute with
identity restriction. Extension of scalars is the left adjoint to restriction along
the constant ring map, so preserves this coproduct and takes the constant k-module k
to the unit O_Y presheaf. This last identification follows by their identical
Hom universal properties: both represent sections of the underlying presheaf.
Tensor with G preserves coproducts, pointwise. The left unitors identify every
O_Y tensor G summand with G. Composing these three isomorphisms gives the result.
This uses no geometry or quasi-coherence. An empty basis is a zero vector space;
extension and tensor preserve its initial object, so the same argument covers it. -/
theorem exists_picard_constant_sections_tensor_basis
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules)
    (I : Type w) (b : Module.Basis I k M) :
    Nonempty ((∐ fun _ : I ↦ G.val) ≅ picardConstantSectionsTensor k Y g M G) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
