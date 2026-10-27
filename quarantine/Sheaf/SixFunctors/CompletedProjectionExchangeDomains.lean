module

public import Sheaf.SixFunctors.CompletedProjectionExchangeData

/-! # A step of the completed projection/base-change diamond

Source: blueprint fix-prop-coherence and fix-prop-projection-formula, projection diamond;
Stacks 0GL1 and 0E48 (blueprint: lem-sf-completed-projection-exchange-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.CompletedProjectionExchange

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {D : FiniteFieldDatum.{u}} (o : Operations l E) (ρ : Realizations l E D o)
  (Q : SixFunctorCompactifiedSquare D)

/-- All four expression domains and their completed endpoint constructibility.
Source: projection diamond, steps 2--6 of
lem-sf-completed-projection-exchange-realization; Stacks 0F0G and 0941
(blueprint: lem-sf-completed-projection-exchange-domains).

Proof: choose common reduction intervals for L and, by integral_residue_tor, K.
Induct on the four expression trees. Pullback preserves the intervals, tensor adds
endpoints, and quasi-compact open extension preserves them by its exactness and
open tensor normalization. At a proper letter choose a finite dimension bound for
its finite-type source and apply directImageCTFEtaleOrigin, widening the upper
endpoint by twice that bound. These choices are independent of the coefficient index.
Reduction inputs are normalized; pullback and tensor preserve normalization. Open
extension commutes with quotient tensors. For proper image its transition-adjoint
is the scalar mate followed by the image of the input transition-adjoint; the
proper etale-origin scalar theorem makes the first factor invertible. Obtain
compatible origins from the normalized actual transitions and reconstruct each
intermediate. Take extrema on a finite affine cover to globalize all bounds.
This gives precisely the recursive domains, including hidden open intermediates.
The same reconstruction and constructibility bounds give the completed endpoints.
Geometric clauses follow recursively from the finite-type square and compactification.
Empty schemes have the zero interval; equal-index quotients have identity transitions.
-/
theorem completedProjectionExchangeDomains (_hl : l ≠ D.p)
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left] [QuasiCompact Q.f.hom.left]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left] [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left)
    (_hK : sfIntegralConstructible l E Q.X.obj.left K)
    (_hL : finiteTorConstructibleIntegral l E Q.Y.obj.left L) :
    (∀ i : Fin 4, (word Q i).geometric ∧
      (word Q i).domain l E o (inputs l E Q K L)) ∧
    sfIntegralConstructible l E Q.Y'.obj.left (integralSource l E Q K L) ∧
    sfIntegralConstructible l E Q.Y'.obj.left (integralTarget l E Q K L) := by sorry

end WeilConjectures.CompletedProjectionExchange
