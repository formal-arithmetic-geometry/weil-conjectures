/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.ExceptionalSystemInterfaces

/-! # Exact and scalar-linear pro-etale operations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (G : StrictEtaleExceptionalAdjoint O ell c S)
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)

variable (P : ExceptionalProCompactSupport O ell c
    CX.proEvaluation CY.proEvaluation CZ.proEvaluation)

/-- The actual pro-etale compact support and site-transported right functor carry
triangulated and coefficient-linear structures.
Source: Zheng Proposition 2.29(2), Construction 5.15 and Lemma 5.22.
(blueprint: lem-sf-exceptional-pro-origin-exact-linear).

Proof: extension by zero is additive and exact, so localization gives its
canonical additive and shift structures and preserves distinguished triangles.
Proper direct image is its universal K-injective right-derived functor and is
triangulated. The site inverse image is exact; the site direct image is a total
right-derived functor. Compose these structures with the recorded triangulated
etale right adjoint. Multiplication by r is the ordinary natural endomorphism
whose component at level n is multiplication by the image of r in the quotient
constant ring sheaf. Its compatibility with transitions is scalar linearity.
Localize that natural transformation on complexes. On representatives each
inverse image, open extension and proper direct image commutes with this scalar;
the universal localization or right-derived property extends the identities to
all derived objects. The etale right adjoint has this property by its recorded
linearity, so the transported right composite has it as well. -/
theorem exceptionalProOriginExactLinear :
    ∃ (leftAdditive : (exceptionalProSupport P).Additive)
      (rightAdditive : (exceptionalSystemRight G CX CY).Additive)
      (leftShift : (exceptionalProSupport P).CommShift ℤ)
      (rightShift : (exceptionalSystemRight G CX CY).CommShift ℤ)
      (scalarX : ExceptionalProScalarAction X O ell)
      (scalarY : ExceptionalProScalarAction Y O ell),
      (@Functor.IsTriangulated _ _ _ _ _ _
        (exceptionalProSupport P) leftShift _ _ _ _ _ _ _ _) ∧
      (@Functor.IsTriangulated _ _ _ _ _ _
        (exceptionalSystemRight G CX CY) rightShift _ _ _ _ _ _ _ _) ∧
      (∀ r M, (exceptionalProSupport P).map ((scalarX.derived r).app M) =
        (scalarY.derived r).app ((exceptionalProSupport P).obj M)) ∧
      (∀ r N, (exceptionalSystemRight G CX CY).map ((scalarY.derived r).app N) =
        (scalarX.derived r).app ((exceptionalSystemRight G CX CY).obj N)) := by
  sorry

end AlgebraicGeometry
