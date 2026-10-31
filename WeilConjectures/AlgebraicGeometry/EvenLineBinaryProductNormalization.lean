/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EvenLineProductIntegrationMaps

/-! # Binary normalization for the concrete even-line product

Source: current blueprint, sec-smooth-purity/sk-prop-sp-composition,
prop-pur-affine-space-composition-law.proof, Steps 3--4.
(blueprint: lem-pur-even-line-binary-product-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.EvenLineProduct
open AffineLinePurity AffineSpacePurity

/-- The concrete binary product in left-associated tensor-power coordinates.
Source: affine-space composition proof Step 3; the reassociation argument in
lem-pur-even-line-product-integration-symmetry, Steps 1--2 and 4
(blueprint: lem-pur-even-line-binary-product-normalization).

Proof: the finite shifted Tate external powers and all intermediate tensors have
bounded etale origin: Tate factors are shifted flat lines, and the compact-support
factors are ctf by hV. Apply the finite triple normal-form theorem in the product
compactification. The two proper words coincide because the ordinary triple
transpose identifies both with the tensor of the three counits. Their open
normalizations coincide by full faithfulness of extension by zero, since both
restrict to the identity. Transport through the canonical compactification and
pullback/tensor comparisons to obtain associativity of forward on coordinate
blocks. Induct on b. For b=0 the equation is the defining inverse equation of
binaryInverse and the recursion for kappa. For b+1 apply that associativity to
blocks of lengths a+1, b+1 and 1, apply the induction hypothesis, and cancel the
specified last binary product. The associator introduced by this step is exactly
the recursive appendPower. All inverses used here are the supplied hprod inverses;
no invertibility of forward a b is assumed. -/
theorem binaryProductNormalization
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (hU : Nonempty (integral P Y 0 ≅ 𝟙_ (D P Y)))
    (hV : ∀ r : ℕ, DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) Y (integral P Y r))
    (hprod : ∀ r : ℕ, IsIso (forward P Y aY r 0))
    (a b : ℕ) :
    tensorHom (kappa P Y aY hprod a).inv (kappa P Y aY hprod b).inv ≫
        forward P Y aY a b =
      (appendPower (integral P Y 0) a b).hom ≫
        (kappa P Y aY hprod (a + b + 1)).inv := by sorry

end AlgebraicGeometry.ProEtale.EvenLineProduct
