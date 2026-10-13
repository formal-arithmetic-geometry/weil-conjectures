/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # ScalarExtCupInverseImage

Source: Stacks Project, Cohomology, Tags 01F7, 01FD, 07MB and 0FKV.
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

attribute [local instance] Sheaf.monoidalCategory HasExt.standard

/-- Exact inverse image transports the Yoneda tensor pairing, including arbitrary
postcomposition maps on its two factors.
Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-scalar-ext-cup-inverse-image).

Proof: The inverse image of sheaves of k-vector spaces is exact and its canonical
oplax tensor comparison is an isomorphism: on stalks it is the identity on the
k-tensor of the two stalks. The unit comparison identifies the inverse image of
the constant sheaf k with the constant sheaf k. This is the same comparison as
scalarInverseUnitIso, since both are the adjoint of the constant section 1.
Expand scalarExtCup as its two tensor-functor transports and Yoneda composition.
Exact-functor transport preserves composition and degree-zero morphisms. The
oplax tensor comparison intertwines inverse image followed by each tensor functor
with the corresponding tensor functor followed by inverse image. Apply naturality
of Ext transport under these comparison transformations. The oplax left-unitor
identity identifies the initial degree-zero morphism, and associativity of Ext
composition gives the equality before postcomposition by phi and psi. Naturality
of tensoring under phi and psi moves these degree-zero morphisms to the two inputs.
Equivalently, apply inverse image to the signed resolution tensor pairing of
Tag 07MB and then the two coefficient morphisms; exactness and Tag 0FKV identify
both augmentations. No signs change, since all comparison maps have degree zero.
The same identities apply in degree zero, for zero sheaves and on empty schemes.
-/
theorem scalarExtCup_inverseImage (t : Y ⟶ X)
    (A B : KSheaf X k) (A' B' : KSheaf Y k)
    (φ : (scalarInverseImage t).obj A ⟶ A')
    (ψ : (scalarInverseImage t).obj B ⟶ B') (p q : ℕ)
    (a : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) A p)
    (b : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) B q) :
    ((Abelian.Ext.mk₀ (scalarInverseUnitIso t).inv).comp
      ((scalarExtCup a b).mapExactFunctor (scalarInverseImage t))
      (zero_add (p + q))).comp
        (Abelian.Ext.mk₀ (((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
            A B ≫ (φ ⊗ₘ ψ))) (add_zero (p + q)) =
      scalarExtCup
        (((Abelian.Ext.mk₀ (scalarInverseUnitIso t).inv).comp
          (a.mapExactFunctor (scalarInverseImage t)) (zero_add p)).comp
            (Abelian.Ext.mk₀ φ) (add_zero p))
        (((Abelian.Ext.mk₀ (scalarInverseUnitIso t).inv).comp
          (b.mapExactFunctor (scalarInverseImage t)) (zero_add q)).comp
            (Abelian.Ext.mk₀ ψ) (add_zero q)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
