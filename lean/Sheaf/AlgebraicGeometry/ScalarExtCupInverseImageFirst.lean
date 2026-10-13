/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # ScalarExtCupInverseImageFirst

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

/-- Compatibility of the first tensor transport with exact inverse image.
Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-scalar-ext-cup-inverse-image-first).

Proof: Put T = scalarInverseImage t, u = scalarInverseUnitIso t, and write δ for the canonical
oplax tensor comparison. Consider the natural transformation from tensorRight 1_X followed by T
to T followed by tensorRight 1_Y with component δ_{M,1_X} followed by id_{TM} tensor u.hom. Its
naturality follows from δ_natural_left and bifunctoriality of tensor. Apply this transformation
termwise to complexes, pass to localization, and use its commutation with shifts: the naturality
square for the shifted morphism representing a is exactly the equality of the two Ext
transports, with degree-zero components given by mk₀. The identity (u.inv followed by
T(λ_{1_X}.inv) followed by δ_{1_X,1_X} followed by id tensor u.hom) = (λ_{1_Y}.inv followed by
u.inv tensor id) identifies their source maps. To obtain it, the oplax right-unitor identity,
together with λ_{1_X} = ρ_{1_X}, λ_{1_Y} = ρ_{1_Y} and naturality of ρ along u.inv, gives the
same formula with its unit comparison η in place of u.hom; these maps agree because their
adjoints under the inverse-image/direct-image adjunction are both the constant section 1 (expand
the constant-sheaf adjunction defining u). Naturality of the unitors and tensor with φ,
preservation of degree-zero morphisms by Ext transport, and associativity now insert φ on both
sides. This proves the stated first-factor formula independently of any b or q. For p=0 all the
Ext maps reduce to the same morphism coherence square; zero sheaves and empty schemes use the
identical square.
-/
theorem scalarExtCup_inverseImage_first (t : Y ⟶ X)
    (A : KSheaf X k) (A' : KSheaf Y k)
    (φ : (scalarInverseImage t).obj A ⟶ A') (p : ℕ)
    (a : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) A p) :
    ((Abelian.Ext.mk₀ (scalarInverseUnitIso t).inv).comp
      (((Abelian.Ext.mk₀ (λ_ (𝟙_ (KSheaf X k))).inv).comp
        (a.mapExactFunctor (tensorRight (𝟙_ (KSheaf X k))))
          (zero_add p)).mapExactFunctor (scalarInverseImage t)) (zero_add p)).comp
      (Abelian.Ext.mk₀ (((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
        A (𝟙_ (KSheaf X k)) ≫ (φ ⊗ₘ (scalarInverseUnitIso t).hom))) (add_zero p) =
    (Abelian.Ext.mk₀ (λ_ (𝟙_ (KSheaf Y k))).inv).comp
      ((((Abelian.Ext.mk₀ (scalarInverseUnitIso t).inv).comp
        (a.mapExactFunctor (scalarInverseImage t)) (zero_add p)).comp
          (Abelian.Ext.mk₀ φ) (add_zero p)).mapExactFunctor
            (tensorRight (𝟙_ (KSheaf Y k)))) (zero_add p) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
