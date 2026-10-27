module

public import Sheaf.Paper.NativeConstantSupportModel

/-! # Computation of the native whole-system reduction counit on K-flat complexes

Source: Stacks 06YY, 0940--0941 and derived adjoint functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The native reduction mate computes ordinary whole-system quotient extension on K-flats.
Source: Stacks, sites-cohomology.tex, Lemma derived-base-change (06YY),
section-derived-limits (0940), Lemma derived-limit-is-ok (0941), and derived.tex,
Lemma derived-adjoint-functors.
Proof: on the ringed sequence site ordinary quotient extension is the composite of
constant diagram formation and extension to the quotient ring sheaf. A K-flat complex
has a K-flat constant diagram: tensor and acyclicity are detected levelwise.
Extension of scalars computes its left derived functor on this diagram. Its right
adjoint is the ordinary inverse limit after coefficient restriction. Deriving this
adjunction identifies the derived left adjoint with S.reduction, since both are left
adjoint to the specified coefficientSequenceLimit. The isomorphism of right adjoints
is reductionRightComparison, normalized by its derived unit on every complex.
Under adjoint transposition the computing left comparison is therefore precisely
systemReductionCounit, defined as the mate of that same right-derived unit.
Its component on the given K-flat complex is consequently invertible. This argument
uses the full sequence site and all its transitions; it also applies to the zero
complex and to the empty site, without a derived-completeness hypothesis.
(blueprint: lem-pur-native-reduction-counit-kflat). -/
theorem nativeReductionCounit_kFlat (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    IsIso ((systemReductionCounit l E W S).app
      ((HomotopyCategory.quotient _ _).obj P)) := by sorry

end WeilConjectures.PurStrictScalar
