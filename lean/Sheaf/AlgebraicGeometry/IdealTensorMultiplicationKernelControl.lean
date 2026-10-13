/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Coherence and annihilation of the ideal tensor multiplication kernel

Source: Stacks Project, Tag 01YB, second Artin-Rees argument.
(blueprint: lem-pc-ideal-tensor-multiplication-kernel-control)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The tensor multiplication source is coherent and its quasi-coherent kernel is
annihilated by the same ideal power.
Source: Stacks Project, Tag 01YB, the short exact sequence preceding the second
Artin-Rees application; Tags 01XZ and 01Y0 for coherence.
(blueprint: lem-pc-ideal-tensor-multiplication-kernel-control)

Proof: On an affine open, the ideal power is a finite module over a Noetherian ring,
and the sections of H are finite. Their tensor product is finite. The affine tensor
comparison gives quasi-coherence and finite type, hence coherence of T = I^n tensor H.
The coherent kernel theorem gives coherence, and hence quasi-coherence, of K = ker(mu).
For a section z of K, write its image as a sum b_j tensor h_j, with sum b_j h_j = 0.
For a in I^n, balancing and commutativity give
 a (sum b_j tensor h_j) = sum a tensor (b_j h_j) = 0.
The kernel inclusion is injective, so a z = 0. The affine product formula identifies
I^n K with zero. The recursive sheaf power has affine range I(U)^n, including n=0,
when it is the structure sheaf; thus this is the stated product vanishing.
Vanishing on the affine basis implies vanishing of the product sheaf.
For n=0 multiplication is the left unitor up to the canonical unit-ideal isomorphism,
so K=0. Zero and unit ideals and the zero module satisfy the same calculation. -/
theorem ideal_tensor_multiplication_kernel_control
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (H : X.Modules)
    (hH : RingedSpace.IsCoherent X.toRingedSpace H) (n : ℕ) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let T := (I ^ n).toModules ⊗ H
    let μ := (I ^ n).toModulesι ▷ H ≫ (λ_ H).hom
    RingedSpace.IsCoherent X.toRingedSpace T ∧
      (kernel μ).IsQuasicoherent ∧
      IsZero (idealModuleProduct (idealSheafPower I.toModulesι n).2 (kernel μ)) := by sorry

end AlgebraicGeometry.Scheme.Modules
