/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PrincipalThickeningObstruction

/-! # Factoring a principal ideal transition through the structure sheaf

Source: Stacks Project, Tag 0H3D, the left vertical map in its diagram.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Bounded principal torsion lets the inclusion of higher powers factor through O_W.

Source: Stacks Project, Tag 0H3D, the map induced by multiplication by g^c.
(blueprint: new-principal-thickening-ideal-factor)

Proof: For each localization R_p, an element a annihilated by g^(n+c+1)
can be written r/s. There is a t outside p with t*g^(n+c+1)*r=0
in R. Apply the uniform annihilation hypothesis to t*r to obtain
g^c*t*r=0, hence g^c a=0 in R_p. Therefore the kernel sheaf of multiplication
by g^(n+c+1) is killed by multiplication by g^c. Multiplication by g^c
thus descends along O_W -> image(g^(n+c+1)) to a map d into O_W, using
the image as the cokernel of the kernel in this abelian category. This map
is determined by d(g^(n+c+1)a)=g^c a. Composing d with multiplication by
g^(n+1) equals the higher ideal inclusion: check after the epic map
O_W -> image(g^(n+c+1)), where the assertion is the power identity
(n+1)+c=(n+c)+1. This is independent of H^1 and of any section to lift.
The case c=0 requires g-torsion to vanish and gives division by g^(n+1).
For g=0 and c positive the source ideal is zero. Unit g gives invertible
multiplication. Empty W has the unique map between zero sheaves. -/
theorem principal_thickening_ideal_factor
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (c n : ℕ)
    (hkill : ∀ (j : ℕ) (s : R), g ^ j * s = 0 → g ^ c * s = 0) :
    ∃ d : principalThickeningIdeal R g W (n + c) ⟶
        SheafOfModules.unit W.toScheme.ringCatSheaf,
      d ≫ principalThickeningMultiplication R g W n =
        image.ι (principalThickeningMultiplication R g W (n + c)) := by sorry

end AlgebraicGeometry.Scheme
