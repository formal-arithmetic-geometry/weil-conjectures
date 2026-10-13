/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Removing ideal-power torsion from a coherent module

Source: Stacks Project, Tag 01YB, second paragraph of the proof.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- A sufficiently high ideal-power product has no ideal-power torsion,
and its inclusion is bijective on sections over the ideal complement.

Source: Stacks Project, Tag 01YB, second paragraph; Tags 01Y8 and 01YA.
(blueprint: lem-pc-coherent-ideal-power-torsion-free-product)

Proof: The quasi-coherent annihilator submodules H_n of I^n form an increasing
chain in H. Noetherian ACC gives r with every H_n contained in T=H_r.
Artin-Rees gives c with I^(r+c)H intersect T contained in I^r T=0.
Take k=r+c and P=I^k H, the actual image of multiplication, not a chosen
existence witness. Ideal products are quasi-coherent. The inclusion P into H
is mono because it is an image inclusion. On the complement I is the unit
ideal, so P restricts to H and the inclusion is bijective on U-sections.
For a section x of P killed locally by I^n, its image in H belongs to H_n
and therefore to T. It also belongs to P; the zero intersection forces its
image to vanish. The mono inclusion is injective on sections, so x=0.
The affine power formula identifies recursive powers with I^n, including
n=0 where annihilation by the unit already forces zero. The same argument
covers empty U, the unit ideal, and the zero module. -/
theorem exists_coherent_idealPower_torsionFree_product
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (H : X.Modules) [H.IsQuasicoherent]
    (hH : RingedSpace.IsCoherent X.toRingedSpace H) (U : X.Opens)
    (hI : (I.support : Set X) = (U : Set X)ᶜ) :
    ∃ k : ℕ,
      let P := idealModuleProduct (idealSheafPower I.toModulesι k).2 H
      let j := idealModuleProductι (idealSheafPower I.toModulesι k).2 H
      P.IsQuasicoherent ∧ Mono j ∧ Function.Bijective (j.val.app (op U)) ∧
      ∀ (n : ℕ) (W : X.Opens) (x : P.val.obj (op W)),
        (∀ (V : X.Opens) (h : V ≤ W)
          (b : (idealSheafPower I.toModulesι n).1.val.obj (op V)),
          ((idealSheafPower I.toModulesι n).2.val.app (op V) b : Γ(X, V)) •
            P.val.map (homOfLE h).op x = 0) → x = 0 := by sorry

end AlgebraicGeometry.Scheme.Modules
