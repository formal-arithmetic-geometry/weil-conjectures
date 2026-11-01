/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierShiftCore

/-! # Compatible shifts for the common-stage dual

Source: thm-coef-qbar-verdier, proof steps 3--4.
(blueprint: lem-coef-qbar-verdier-shift-compatibility)

The finite shift comparisons descend and carry distinguished triangles to
distinguished triangles. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.haveILetI false

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

/-- The finite exact dualities admit shift structures compatible with the normalized
common-stage comparisons.
Source: thm-coef-qbar-verdier, coefficient descent and exactness in proof steps 3--4.
(blueprint: lem-coef-qbar-verdier-shift-compatibility)

Proof: choose the shift comparison of each rational Verdier duality from its
construction as internal Hom into the dualizing complex. The Hom shift adjunction
identifies duality of a negative shift with the positive shift of the dual. Its
zero and addition laws are the corresponding Hom shift laws. Rational scalar
extension preserves these adjunctions and their evaluations; the normalized beta
comparison is their unique evaluation transpose, so its square with these shift
comparisons commutes. Include these comparisons at each object's coefficient
stage. More explicitly, on an object included from E its component is the
composite of: V applied to the inverse opposite-inclusion shift comparison;
the inverse r_E at the shifted finite object; inclusion of the finite dual
shift comparison; the inclusion shift comparison at the finite dual; and
the shifted r_E. This starts at V of the shifted included object and ends
at the shifted V of that object. Conjugating along beta compares the same
formula at a larger coefficient field; the beta shift square makes the two
expressions agree. Apply this at the field of an arbitrary arrow representative.
The square just established makes these components natural on quotient morphisms,
and their finite zero and addition laws give a CommShift structure on the
descended functor. Its comparison with each finite dual commutes with shifts by
construction. The chosen finite structures are the exact rational Verdier
structures, so each finite dual remains triangulated. This lemma asserts only
shift coherence and finite exactness; it makes no assertion about the image of
an arbitrary distinguished triangle in the pair category. -/
theorem descended_shift_compatibility (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) :
    ∃ s : (descendedDual D l hl Ω X F hF).CommShift ℤ,
      letI := s
      ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
        ∃ t : (F.datum E).dual.CommShift ℤ,
          letI := t
          (F.datum E).dual.IsTriangulated ∧
          let J := GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E
          let jshift : J.CommShift ℤ :=
            GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E
          let oshift : J.op.CommShift ℤ :=
            @Pretriangulated.Opposite.commShiftFunctorOpInt _ _ _ _ _ _ J jshift
          let cA : ((F.datum E).dual ⋙ J).CommShift ℤ :=
            @Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual J ℤ _ _ _ _ t jshift
          let cB : (J.op ⋙ descendedDual D l hl Ω X F hF).CommShift ℤ :=
            @Functor.CommShift.comp _ _ _ _ _ _ J.op
              (descendedDual D l hl Ω X F hF) ℤ _ _ _ _ oshift s
          @NatTrans.CommShift _ _ _ _ _ _
            (descendedComparison D l hl Ω X F hF E).hom ℤ _ _ _ cA cB := by
  classical
  obtain ⟨t, ht, hnat⟩ := finite_shift_naturality D l hl Ω X F hF
  obtain ⟨s, hs⟩ := descended_shift_core D l hl Ω X F hF t hnat
  letI := s
  refine ⟨s, ?_⟩
  intro E
  letI := t E
  refine ⟨t E, ht E, ?_⟩
  exact hs E

end WeilConjectures.CoefQbarVerdier
