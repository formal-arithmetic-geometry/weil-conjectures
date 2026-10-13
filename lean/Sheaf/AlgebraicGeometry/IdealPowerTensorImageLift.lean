/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Lifting a higher ideal-product image into an ideal-power tensor product

Source: Stacks Project, Tag 01YB, proof of lemma-homs-over-open, the second
Artin-Rees argument for the kernel of tensor multiplication.
(blueprint: lem-pc-ideal-power-tensor-image-lift)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- A sufficiently high ideal product lifts through tensor multiplication.
Source: Stacks Project, Tag 01YB, proof of lemma-homs-over-open, the kernel K and
its zero intersection with a high ideal power of the tensor product.
(blueprint: lem-pc-ideal-power-tensor-image-lift)

Proof: Set T = I^n tensor H and let mu : T -> H be multiplication. Both T and its
kernel K are coherent on the Noetherian scheme. On an affine open, a tensor in K
is a sum of b_j tensor h_j with sum b_j h_j = 0. For a in I^n, balancing gives
a times this sum = a tensor (sum b_j h_j) = 0, so I^n K = 0. Artin-Rees supplies
c such that K intersect I^m T is contained in I^(m-c) K for m >= c. Take m >= c+n;
the intersection is zero. Multiplication maps I^m T onto I^(n+m) H: on affine
sections its image is I^m I^n H = I^(n+m) H. Its restriction is therefore an
isomorphism of I^m T onto that image. Compose its inverse with I^m T -> T to
obtain a, whose composite with mu is the product inclusion. The affine basis
and sheaf gluing identify these products with the ideal-sheaf-data powers.
At n=0 take m=0 and use the inverse left unitor on the multiplication image.
For a zero or unit ideal and a zero module the same argument applies; it uses
neither an open subset nor a target module nor an extended morphism. -/
theorem ideal_power_tensor_image_lift
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (H : X.Modules)
    (hH : RingedSpace.IsCoherent X.toRingedSpace H) (n : ℕ) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    ∃ (m : ℕ) (a : idealModuleProduct (I ^ (n + m)).toModulesι H ⟶
        (I ^ n).toModules ⊗ H),
      a ≫ ((I ^ n).toModulesι ▷ H ≫ (λ_ H).hom) =
        idealModuleProductι (I ^ (n + m)).toModulesι H := by
  sorry

end AlgebraicGeometry.Scheme.Modules
