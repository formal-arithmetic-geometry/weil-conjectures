/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # ScalarExtCupInverseImageSecond

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

/-- Compatibility of the second tensor transport with exact inverse image.
Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-scalar-ext-cup-inverse-image-second).

Proof: Put T = scalarInverseImage t and u = scalarInverseUnitIso t. For fixed A,
the components δ_{A,M}
form a natural transformation from tensorLeft A followed by T to T followed by tensorLeft (TA),
by δ_natural_right. The morphisms φ tensor id form a second natural transformation from
tensorLeft (TA) to tensorLeft A'. Apply these transformations termwise to complexes. Exactness
of all functors ensures that they descend through quasi-isomorphism localization; the termwise
maps commute with shifts. Naturality on the shifted morphism representing b therefore gives
T(tensorLeft A b), postcomposed by δ_{A,B} and φ tensor id, equal to δ_{A,1_X} followed by φ
tensor id, then tensorLeft A' of Tb, in Ext. Postcompose by A' tensor ψ. Tensor functors
preserve degree-zero maps and Ext composition. Insert u.hom followed by u.inv = id at the
intermediate factor T1_X: after tensorLeft A', this places u.hom in the source comparison and
u.inv before Tb. Associativity of Ext composition gives exactly the displayed formula, with no
use of a or p or the first-factor formula. Every inserted map has degree zero. In q=0 the
calculation is ordinary δ naturality, tensor bifunctoriality, and u.hom_inv_id; for zero sheaves
or empty schemes the same identities hold.
-/
theorem scalarExtCup_inverseImage_second (t : Y ⟶ X)
    (A B : KSheaf X k) (A' B' : KSheaf Y k)
    (φ : (scalarInverseImage t).obj A ⟶ A')
    (ψ : (scalarInverseImage t).obj B ⟶ B') (q : ℕ)
    (b : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) B q) :
    ((b.mapExactFunctor (tensorLeft A)).mapExactFunctor (scalarInverseImage t)).comp
      (Abelian.Ext.mk₀ (((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
        A B ≫ (φ ⊗ₘ ψ))) (add_zero q) =
    (Abelian.Ext.mk₀ (((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
      A (𝟙_ (KSheaf X k)) ≫ (φ ⊗ₘ (scalarInverseUnitIso t).hom))).comp
      ((((Abelian.Ext.mk₀ (scalarInverseUnitIso t).inv).comp
        (b.mapExactFunctor (scalarInverseImage t)) (zero_add q)).comp
          (Abelian.Ext.mk₀ ψ) (add_zero q)).mapExactFunctor (tensorLeft A'))
            (zero_add q) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
