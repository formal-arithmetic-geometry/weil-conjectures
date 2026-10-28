/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # Explicit finite-stage components of the Verdier shift comparison

Source: thm-coef-qbar-verdier, proof steps 3--4. The finite shifts must be chosen
compatibly with the normalized evaluation transposes before they can descend.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open GeneralAlgebraicallyClosedCoefficients (Stage inclusion)

/-- Transport the finite dual shift along its specified inclusion comparison. -/
@[irreducible] def finiteRestrictionShift (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω, (F.datum E).dual.CommShift ℤ)
    (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    ((inclusion (Y := X) E).op ⋙ descendedDual D l hl Ω X F hF).CommShift ℤ := by
  letI : ((F.datum E).dual ⋙ inclusion (Y := X) E).CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual (inclusion (Y := X) E)
      ℤ _ _ _ _ (t E) (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E)
  exact Functor.CommShift.ofIso (descendedComparison D l hl Ω X F hF E) ℤ

/-- Transport along the specified comparison makes that comparison commute with shifts. -/
theorem finiteRestrictionShift_compatibility (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω, (F.datum E).dual.CommShift ℤ)
    (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    let cA : ((F.datum E).dual ⋙ inclusion (Y := X) E).CommShift ℤ :=
      @Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual (inclusion (Y := X) E)
        ℤ _ _ _ _ (t E) (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E)
    @NatTrans.CommShift _ _ _ _ _ _
      (descendedComparison D l hl Ω X F hF E).hom ℤ _ _ _ cA
      (finiteRestrictionShift D l hl Ω X F hF t E) := by
  unfold finiteRestrictionShift
  exact @Functor.CommShift.ofIso_compatibility _ _ _ _ _ _
    (descendedComparison D l hl Ω X F hF E) ℤ _ _ _
    (@Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual (inclusion (Y := X) E)
      ℤ _ _ _ _ (t E) (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E))

/-- The only possible shift component at a pair, prescribed by its finite stage.
The inverse inclusion comparison first moves the shifted pair back to its stage. -/
def shiftComponent (F : Finite D l hl Ω X) (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω, (F.datum E).dual.CommShift ℤ)
    (n : ℤ) (P : (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ) :
    (descendedDual D l hl Ω X F hF).obj (P⟦n⟧) ≅
      ((descendedDual D l hl Ω X F hF).obj P)⟦n⟧ :=
  let J := (inclusion (Y := X) P.unop.stage).op
  let V := descendedDual D l hl Ω X F hF
  letI := finiteRestrictionShift D l hl Ω X F hF t P.unop.stage
  (V.mapIso ((J.commShiftIso n).app (op P.unop.obj))).symm ≪≫
    ((J ⋙ V).commShiftIso n).app (op P.unop.obj)

/-- Canonical finite internal-Hom shifts make the explicit components natural on
common-stage quotient arrows.
Source: blueprint thm-coef-qbar-verdier, proof steps 3--4, evaluation transpose and
finite-representative descent (blueprint: lem-coef-qbar-verdier-shift-naturality-K6).

Proof: use the signed reindexing of the internal Hom complex to define each finite
shift comparison. The tensor--Hom adjunction identifies it with the evaluation
transpose of the tensor shift comparison. The cone formula makes these the exact
finite Verdier shifts. A normalized scalar-extension beta preserves evaluation;
transposing its square shows that beta commutes with these chosen shifts. Represent
an arbitrary pair arrow over a common finite overfield. Finite naturality gives the
square there. The beta shift squares identify its two ends with the components at
the original source and target fields. Tower coherence makes this independent of
the representative. Hence the displayed naturality equation holds on the quotient.
Only this arrow equation is asserted here: zero and addition coherence and the
finite inclusion comparison are proved separately by categorical cancellation. -/
theorem finite_shift_naturality (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) :
    ∃ t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
        (F.datum E).dual.CommShift ℤ,
      (∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
        letI := t E
        (F.datum E).dual.IsTriangulated) ∧
      ∀ (n : ℤ) (P Q : (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ)
        (f : P ⟶ Q),
        (descendedDual D l hl Ω X F hF).map (f⟦n⟧') ≫
          (shiftComponent D l hl Ω X F hF t n Q).hom =
        (shiftComponent D l hl Ω X F hF t n P).hom ≫
          ((descendedDual D l hl Ω X F hF).map f)⟦n⟧' := by sorry

end WeilConjectures.CoefQbarVerdier
