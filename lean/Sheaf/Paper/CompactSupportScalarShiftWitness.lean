module

public import Sheaf.Paper.CompactSupportScalarShiftStructures

/-! # Canonical shifts of scalar compact-support comparison maps

Source: Stacks 05SU, 06YU, 0B56, 0941 and 03DJ; auxiliary comparison Steps 12--13
(blueprint: lem-pur-compact-support-scalar-shift-normalization).
The data helpers expose canonical shifts of existing functors. The theorem retains
proper/open, strict-tower, signed Roos, and completed total-limit equations.
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
section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- Normalized completed scalar witness and its shift square.
Source: Stacks Tags 0941, 099I and 099L; Step 9 of
lem-pur-compact-support-scalar-shift-normalization.
(blueprint: lem-pur-compact-support-scalar-shift-witness).

Proof: obtain gamma and its exact factorization and completeness conclusions
from compactSupportScalarLimitReduction. Integral triangulated closure
(lem-pur-integral-ctf-shift-closure) supplies membership of each M[r]. The
scalarLimitArrow square is the last clause of scalarLimitConstraintShift.
Conjugate scalarLimitArrow by scalarCompletion and the support/limit
isomorphisms; their canonical shift squares (scalarLimitConstraintShift) produce
a shift-compatible beta on constant restrictions. The exact factorization gives
restriction(gamma)=beta by cancellation. Both support objects are complete.
Finite-free scalar extension preserves completeness by finite sums, and shifts
preserve completeness. The normalized constant/completed equivalence is fully
faithful on these objects. Restrict the gamma equation, use naturality of the
restriction shift, and substitute the two factorization equations at M and M[r].
The result is beta's shift square, so faithfulness proves it. This works for all
integer shifts, including zero and negative shifts; positive e is used only for
inverse arithmetic restriction. -/
theorem compactSupportScalarShiftWitness (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    ∃ γ : (finiteTorConstructibleIntegral l E X).ι ⋙ scalarSupport l E c S ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i Y) ⟶
      (finiteTorConstructibleIntegral l E X).ι ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙ scalarSupport l F c S',
      ∀ M : finiteTorConstructibleIntegralCategory l E X,
        ((baseTensor l E F i Y).map
            ((scalarSupportLimit l E c S).hom.app M.obj) ≫
          scalarLimitArrow l E F i c S S' e he hepos M.obj =
        (scalarCompletion l E F i Y).hom.app ((scalarSupport l E c S).obj M.obj) ≫
          (scalarConstantRestriction l F Y).map (γ.app M) ≫
          (scalarSupportLimit l F c S').hom.app
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)) ∧
      (∀ r : ℤ, ∃ hMr : finiteTorConstructibleIntegral l E X (M.obj⟦r⟧),
        γ.app ⟨M.obj⟦r⟧, hMr⟩ ≫
            ((pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙
              scalarSupport l F c S').commShiftIso r).hom.app M.obj =
          ((scalarSupport l E c S ⋙
            pbcDerivedExtend (completedCoefficientMap l E F i Y)).commShiftIso r).hom.app
              M.obj ≫ (γ.app M)⟦r⟧') := by sorry

end Geometry
end WeilConjectures.PurStrictScalar
