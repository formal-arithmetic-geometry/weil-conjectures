module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Contracting points of a cocharacter

Source: Milne, Algebraic Groups (2017), Section 13d and Theorem 13.33, pp.265--266
(blueprint: def-sfb-cocharacter-contracting-points).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.CocharacterContraction

/-- The punctured affine line inclusion, given by the coordinate substitution t ↦ t.
Source: Milne, Section 13d (blueprint: def-sfb-cocharacter-contracting-points). -/
def puncturedLine (F : Type u) [Field F] :
    StandardGroupSchemes.multiplicative F ⟶ StandardGroupSchemes.additive F :=
  StandardGroupSchemes.map F (Polynomial.aeval (LaurentPolynomial.T 1))

/-- A family g contracts to the identity if its conjugation orbit on Gₘ × W extends
across A¹ × W, with identity value on the zero section. The test scheme W may be
nonreduced. This is a condition on actual maps, not on rational points alone.
Source: Milne, Section 13d and Theorem 13.33, pp.265--266
(blueprint: def-sfb-cocharacter-contracting-points). -/
def Contracts {F : Type u} [Field F] (G : Grp (Over (Spec (.of F))))
    (cochar : Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ G)
    (W : Over (Spec (.of F))) (g : W ⟶ G.X) : Prop :=
  ∃ f : StandardGroupSchemes.additive F ⊗ W ⟶ G.X,
    (puncturedLine F ⊗ₘ 𝟙 W) ≫ f =
      (fst (StandardGroupSchemes.multiplicative F) W ≫ cochar.hom.hom) *
        (snd (StandardGroupSchemes.multiplicative F) W ≫ g) *
        (fst (StandardGroupSchemes.multiplicative F) W ≫ cochar.hom.hom)⁻¹ ∧
    lift (toUnit W ≫ η[StandardGroupSchemes.additive F]) (𝟙 W) ≫ f = 1

end AlgebraicGeometry.CocharacterContraction
