/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemScalarProjectionData

/-! # Fixed basis distributivity

Source: proof of lem-coef-system-scalar-projection-identification, Steps 1 and 5.
(blueprint: lem-coef-system-scalar-basis-distributivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.leftAdjoint
  HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open WeilConjectures.SemilinearSections WeilConjectures.FiniteFreeSystemRestriction
namespace WeilConjectures.SystemScalarProjection

variable (l : ℕ) [Fact l.Prime]
  (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L) {K : FiniteFieldDatum.{u}} {d : ℕ}
  {b : Fin d → Padic.coefficientExtensionIntegers l L} {ramification : ℕ}
  (s : Assertions l E L i K d b ramification)

/-- The fixed reduced basis gives coordinates commuting with compact support.
Source: scalar projection identification, Steps 1 and 5.
(blueprint: lem-coef-system-scalar-basis-distributivity).
Proof: at (n,V), use the reductions of the fixed integral basis to write a section
of restricted extension uniquely as a sum of basis multiples of scalar generators.
The coordinate identities follow from the inverse coefficient matrix; since all
basis vectors come from S, these maps commute with quotient transitions and site
restrictions. Apply them degreewise to complexes and localize, using the scalar
model counit for the representative formula. Proper direct image preserves finite
products and open extension preserves finite sums. Counit naturality identifies
properScalar on each inclusion with direct image of that inclusion. Open balancing
has the same property on the open and both sides vanish on the complement. Their
composite gives Distributivity for every compactification. -/
theorem scalar_basis_distributivity (X Y : Spaces K) (f : X.val.left ⟶ Y.val.left) :
    ∃ z : BasisCoordinates l E L i s,
      ∀ (c : Compactification f) (M : Derived (A l E) (aTransition l E) X.val.left),
        z.Distributivity l E L i s X Y c M := by sorry

end WeilConjectures.SystemScalarProjection
