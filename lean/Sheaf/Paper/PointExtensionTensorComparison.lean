/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.PointDerivedHomModels

/-! # Balanced tensor comparison for extension from the point

Source: Stacks Tags 03EK and 012Z.
(blueprint: lem-pod-point-extension-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.PointDerivedHom

variable (k : Type u) [Field k] {R : CommRingCat.{u + 1}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
  (α : constantRing.{u, u} k R ⟶ B)
  (L : ModuleCat.{u + 1} R ⥤ Modules.{u, u} k B)
  (hobj : ∀ M : ModuleCat.{u + 1} R, L.obj M = extensionObject.{u, u} k B α M)
  (adj : L ⊣ sections.{u, u} k B α)

/-- Scalar extension commutes with the signed total tensor, through the
multiplication-normalized balancing isomorphism.
Source: Stacks Tags 03EK (tensor sheaves) and 012Z (signed totalization)
(blueprint: lem-pod-point-extension-tensor-comparison).

Proof: on module tensor generators send (b tensor x) tensor (c tensor y)
to bc tensor (x tensor y). The inverse sends b tensor (x tensor y) to
(b tensor x) tensor (1 tensor y). Scalar balancing makes both maps well-defined;
the tensor relations prove both composites are identities. First descend the
constant-module sheafification and then the coefficient tensor sheafification.
Their universal properties also give naturality in both module arguments.
In total degree n take the sum over p+j=n. L is a left adjoint and preserves
these coproducts. The comparison commutes with each differential because both
routes are dx tensor y plus (-1)^p times x tensor dy. The degree maps therefore
form inverse chain maps with exactly the displayed generator formula. -/
theorem point_extension_tensor_comparison
    (hmap : ∀ {M N : ModuleCat.{u + 1} R} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫ extensionMorphism.{u, u} k B α f ≫
        eqToHom (hobj N).symm)
    (P Q : CochainComplex (ModuleCat.{u + 1} R) ℤ) :
    ∃ β : total.{u, u} k B ((extensionComplex.{u, u} k B α L adj).obj P)
        ((extensionComplex.{u, u} k B α L adj).obj Q) ≅
      (extensionComplex.{u, u} k B α L adj).obj (moduleTotal P Q),
      ∀ (p j : ℤ) (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
        (b c : B.obj.obj U) (x : P.X p) (y : Q.X j),
        (β.hom.f (p + j)).val.app U
          (totalElement.{u, u} k B ((extensionComplex.{u, u} k B α L adj).obj P)
            ((extensionComplex.{u, u} k B α L adj).obj Q) p j U
            (generator.{u, u} k B α L hobj (P.X p) U b x)
            (generator.{u, u} k B α L hobj (Q.X j) U c y)) =
          generator.{u, u} k B α L hobj ((moduleTotal P Q).X (p + j)) U (b * c)
            (moduleTotalElement P Q p j x y) := by
  sorry

end WeilConjectures.PointDerivedHom
