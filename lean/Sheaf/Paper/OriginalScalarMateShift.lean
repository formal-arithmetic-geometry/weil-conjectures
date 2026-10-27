module

public import Sheaf.Paper.CompactSupportScalarShiftStructures

/-! # OriginalScalarMateShift

Source: Stacks Project; canonical scalar shifts
(blueprint: lem-pur-original-scalar-mate-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
/-- Shift compatibility on the original ringed sites.
Source: Stacks Tags 07A6, 0B56, 0E8I and 05SU; Steps 2--4 of
lem-pur-compact-support-scalar-shift-normalization.
(blueprint: lem-pur-original-scalar-mate-shift).

Proof: normalize scalar shifts by the universal counit. On a K-flat model the
balanced pullback/scalar comparison sends both shifted tensors to the same tensor;
the coefficient has degree zero, so its tensor shift sign is one. The derived
geometric adjunction counit commutes with shift. Transposing the shifted proper
mate therefore gives the shift of its original transpose; injectivity of the
adjunction Hom bijection gives the proper square. For open extension by zero,
both maps on a presheaf generator indexed by V to X send x tensor b to the same
indexed generator. Sheafification preserves this equality and both differentials
have the same integer-shift sign. These arguments also give the inverse balanced
comparison and the counit square, for every integer, including zero and negative
integers. No flatness hypothesis on the scalar map is required. -/
theorem originalScalarMateShift {R₀ S₀ : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R₀ S₀) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : OriginalMateShift a c := by sorry

end WeilConjectures.PurStrictScalar
