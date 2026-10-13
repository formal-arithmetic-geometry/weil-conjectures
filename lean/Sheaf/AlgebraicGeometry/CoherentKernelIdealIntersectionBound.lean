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

/-! # Bounding an intersection with a coherent multiplication kernel

Source: Stacks Project, Tag 01YA, applied to a quasi-coherent kernel.
(blueprint: lem-pc-coherent-kernel-ideal-intersection-bound)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A high ideal multiple of a coherent source intersects its kernel only inside
any prescribed ideal multiple of the kernel.
Source: Stacks Project, Tag 01YA, the inclusion clause of Artin-Rees, as applied
in Tag 01YB to the kernel of tensor multiplication.
(blueprint: lem-pc-coherent-kernel-ideal-intersection-bound)

Proof: Apply Artin-Rees to the quasi-coherent subsheaf kernel(mu) of the coherent
module F. Its inclusion is monic. There is c such that I^m F intersect kernel(mu)
is contained in I^(m-c) kernel(mu) for every m >= c. Set m=c+n; then m-c=n.
The recursive sheaf powers compute the same powers as the affine ideals, also
at zero. On any open W, represent these subsheaves by the ranges of their
inclusion maps. The Artin-Rees inclusion is exactly the displayed subset.
Alternatively obtain c from module Artin-Rees on a finite affine cover and take
the maximum of the bounds. On subopens the affine sheaf comparison gives the
same inclusion; local membership in the range of a monomorphism glues, so it
holds on every W. No coherence of H or annihilation of the kernel is assumed.
For an empty scheme use c=0. For n=0 the kernel inclusion itself contains the
intersection; for a zero or unit ideal the same Artin-Rees argument applies. -/
theorem coherent_kernel_ideal_intersection_bound
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F H : X.Modules) (μ : F ⟶ H)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hK : (kernel μ).IsQuasicoherent) (n : ℕ) :
    ∃ m : ℕ, ∀ W : X.Opens,
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι m).2 F).app W) ∩
          Set.range ((kernel.ι μ).app W) ⊆
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2
          (kernel μ) ≫ kernel.ι μ).app W) := by sorry

end AlgebraicGeometry.Scheme.Modules
