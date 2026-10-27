module

public import Sheaf.Paper.CompactSupportScalarShiftStructures

/-! # StrictScalarMateShift

Source: Stacks Project; canonical scalar shifts
(blueprint: lem-pur-strict-scalar-mate-shift).
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
/-- The diagram-site scalar mates and their actual support-tower composite shift.
Source: Stacks Tags 07A6, 0B56, 0E8I, 0940; Steps 2--5 of
lem-pur-compact-support-scalar-shift-normalization.
(blueprint: lem-pur-strict-scalar-mate-shift).

Proof: work on the small ringed diagram site before evaluating levels. Balanced
pullback and degree-zero tensor commute with shifts on resolving complexes.
The diagram adjunction counit has its canonical shift compatibility. Transpose
the proper scalar mate: the two shifted transposes agree, hence the mates agree
by the Hom bijection. For the open scalar map, check indexed presheaf generators
and sheafify, with the same differential sign on both sides. Whisker and compose
these two squares in the prescribed order. The support models and reduction
balancing are fixed by their whole-system adjunction units, so their shifted
comparisons agree by adjunction uniqueness. Arithmetic selection only reindexes
terms and composes transitions; it preserves the differential. Thus every factor
of arrow commutes with shift, and their composite does as well. This proves an
equality of strict derived tower maps, not merely of evaluated maps. -/
theorem strictScalarMateShift {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    NatTrans.CommShift (proper l E F i c.g) ℤ ∧
    NatTrans.CommShift (openTensor l E F i c.i) ℤ ∧
    NatTrans.CommShift (strictScalarPull l E F i c.g).inv ℤ ∧
    NatTrans.CommShift
      (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.g).counit ℤ ∧
    NatTrans.CommShift (arrow l E F i c S S' e he hepos) ℤ := by sorry

end WeilConjectures.PurStrictScalar
