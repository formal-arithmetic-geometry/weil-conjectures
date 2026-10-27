module

public import Sheaf.Paper.RelativeProductFactors

/-! Core coefficient squares for the relative-product factors.

Source: the six individual factor-square calculations
(blueprint: lem-sf-relative-product-coefficient-factor-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The six recursively defined coefficient squares are the primitive factor-square
calculation used by the relative-product theorem.
Source: coefficient-factor equation and proof steps 1--5
(blueprint: lem-sf-relative-product-coefficient-factor-squares).

Proof: expand each of the six displayed factors.  The composition, projection,
exchange, and tensor fields of `RelativeProductCoefficientData` give the primitive
squares; whiskering and tensor bifunctoriality paste them with the recursively
defined object comparisons.  Inverse factors use the inverse-square cancellation
identity.  The six resulting component equations are exactly `FactorSquares`.
-/
theorem relative_product_factor_squares_core
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {s s' : PodCoefficientStage} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    {R : RelativeProductPresentation S s Q} {R' : RelativeProductPresentation S' s' Q}
    (A : RelativeProductCoefficientData R R')
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) : A.FactorSquares cg ch := by
  sorry

end WeilConjectures
