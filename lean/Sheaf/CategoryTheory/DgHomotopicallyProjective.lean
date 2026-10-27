/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.DgBimoduleModels

/-!
# Homotopically projective right DG modules

Source: Stacks Project, dga.tex, Tags 09KM and 09KY, Hom-complex vanishing condition
(blueprint: def-sfb-dg-homotopically-projective).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.DgAlgebra

/-- Homotopical projectivity is acyclicity of the right-linear Hom cochains into
any acyclic right DG module. In every integer degree, every closed right-linear
cochain must be the differential of a right-linear cochain one degree lower.
The differential is d f - (-1)^r f d; homogeneous right linearity has no sign.
Source: Stacks Project, dga.tex, Tags 09KM and 09KY, the Hom-complex vanishing
used in the proof of the derived Hom comparison
(blueprint: def-sfb-dg-homotopically-projective). -/
def IsHomotopicallyProjective (A : Algebra.{u}) (P : RightModule A) : Prop :=
  ∀ (N : RightModule A), ((underlying A).obj N).Acyclic →
    ∀ (r : ℤ)
      (f : CochainComplex.HomComplex.Cochain
        ((underlying A).obj P) ((underlying A).obj N) r),
      IsRightLinearCochain A ((underlying A).obj P) (rightAction A P) N r f →
      CochainComplex.HomComplex.δ r (r + 1) f = 0 →
      ∃ g : CochainComplex.HomComplex.Cochain
          ((underlying A).obj P) ((underlying A).obj N) (r - 1),
        IsRightLinearCochain A ((underlying A).obj P) (rightAction A P) N (r - 1) g ∧
        CochainComplex.HomComplex.δ (r - 1) r g = f

end CategoryTheory.DgAlgebra
