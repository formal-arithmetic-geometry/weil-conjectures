/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # Common-stage shift descent core

Source: thm-coef-qbar-verdier, proof steps 3--4.
(blueprint: lem-coef-qbar-verdier-shift-core-Y3)

The finite shift comparisons descend to the common-stage dual and commute with
its normalized finite-stage comparisons. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open GeneralAlgebraicallyClosedCoefficients (Stage)
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

/-- The common-stage shift and its finite comparison squares exist.
Source: thm-coef-qbar-verdier, coefficient descent and exactness in proof steps 3--4.
(blueprint: lem-coef-qbar-verdier-shift-core-Y3)

Proof: choose the canonical integer shift at each finite rational stage from the
internal-Hom construction. The beta comparisons are normalized evaluation
transposes, so their shift squares commute after evaluation; the resulting
components are natural on the quotient pair category and satisfy the zero and
addition laws. Descending these components gives the common-stage CommShift,
and its identity-representative comparison has the required NatTrans.CommShift
structure. -/
theorem descended_shift_core (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      (F.datum E).dual.CommShift ℤ)
    (htri : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      letI := t E
      (F.datum E).dual.IsTriangulated) :
    ∃ s : (descendedDual D l hl Ω X F hF).CommShift ℤ,
      letI := s
      ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
        letI := t E
          let J := GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E
          let jshift : J.CommShift ℤ :=
            GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E
          let oshift : J.op.CommShift ℤ :=
            @Pretriangulated.Opposite.commShiftFunctorOpInt _ _ _ _ _ _ J jshift
          let cA : ((F.datum E).dual ⋙ J).CommShift ℤ :=
            @Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual J ℤ _ _ _ _ (t E) jshift
          let cB : (J.op ⋙ descendedDual D l hl Ω X F hF).CommShift ℤ :=
            @Functor.CommShift.comp _ _ _ _ _ _ J.op
              (descendedDual D l hl Ω X F hF) ℤ _ _ _ _ oshift s
          @NatTrans.CommShift _ _ _ _ _ _
            (descendedComparison D l hl Ω X F hF E).hom ℤ _ _ _ cA cB := by
  sorry

end WeilConjectures.CoefQbarVerdier
