/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierShiftComponents
import WeilConjectures.SixFunctors.CoefQbarVerdier.ShiftDescent.ShiftDescentAssembly

/-! # Common-stage shift descent core

Source: thm-coef-qbar-verdier, proof steps 3--4.
(blueprint: lem-coef-qbar-verdier-shift-core-Y3)

The finite shift comparisons descend to the common-stage dual and commute with
its normalized finite-stage comparisons. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
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
open ShiftDescent
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

-- STATEMENT-DISPUTED: the former premise allowed arbitrary exact finite shifts.
-- Exactness does not make their beta squares commute: over a geometric point,
-- split triangles allow degree-n twists by independent nonzero scalars to the n-th power.
-- The corrected statement below assumes the actual component naturality it needs.
/-- Natural explicit finite components assemble into a coherent integer shift.
Source: thm-coef-qbar-verdier, proof steps 3--4
(blueprint: lem-coef-qbar-verdier-shift-core-Y3).

Proof: form a natural isomorphism in each degree from the explicit components.
Precomposing with each opposite stage inclusion recovers the transported finite
shift structure by cancellation of its inclusion isomorphism. Every object is
literally in its own coefficient stage, so the finite zero and addition laws
imply the global laws. The comparison commutes with shifts by transport along
its defining natural isomorphism. Naturality, rather than mere triangulatedness
of arbitrary finite shifts, is the compatibility needed for this argument. -/
theorem descended_shift_core (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      (F.datum E).dual.CommShift ℤ)
    (hnat : ∀ (n : ℤ)
      (P Q : (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ) (f : P ⟶ Q),
      (descendedDual D l hl Ω X F hF).map (f⟦n⟧') ≫
        (shiftComponent D l hl Ω X F hF t n Q).hom =
      (shiftComponent D l hl Ω X F hF t n P).hom ≫
        ((descendedDual D l hl Ω X F hF).map f)⟦n⟧') :
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
  let V := descendedDual D l hl Ω X F hF
  let J (E : AlgebraicallyClosedCoefficients.Index l Ω) :=
    (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E).op
  letI (E : AlgebraicallyClosedCoefficients.Index l Ω) : (J E).CommShift ℤ :=
    @Pretriangulated.Opposite.commShiftFunctorOpInt _ _ _ _ _ _
      (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E)
      (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E)
  let c E := finiteRestrictionShift D l hl Ω X F hF t E
  let e (n : ℤ) : shiftFunctor _ n ⋙ V ≅ V ⋙ shiftFunctor _ n :=
    NatIso.ofComponents (shiftComponent D l hl Ω X F hF t n) (hnat n _ _)
  have he (E : AlgebraicallyClosedCoefficients.Index l Ω) (n : ℤ) :
      precompShift (J E) V n (e n) = (c E).commShiftIso n := by
    ext K
    rw [precompShift_hom]
    dsimp only [e, NatIso.ofComponents, shiftComponent]
    dsimp only [J, Functor.op_obj, Functor.comp_obj,
      GeneralAlgebraicallyClosedCoefficients.inclusion, CategoryTheory.StageSystem.ι] at *
    simp only [V, op_unop, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
      ← Functor.map_comp_assoc]
    dsimp only [Iso.app]
    erw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  let s := assembleShift J (fun P ↦ ⟨P.unop.stage, op P.unop.obj, rfl⟩) V c e he
  refine ⟨s, ?_⟩
  intro E
  letI := t E
  letI : V.CommShift ℤ := s
  letI : (J E ⋙ V).CommShift ℤ := c E
  let cA : ((F.datum E).dual ⋙
      GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E).CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual
      (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E) ℤ _ _ _ _
      (t E) (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E)
  letI := cA
  have hc : @NatTrans.CommShift _ _ _ _ _ _
      (descendedComparison D l hl Ω X F hF E).hom ℤ _ _ _ cA (c E) :=
    finiteRestrictionShift_compatibility D l hl Ω X F hF t E
  have hc' :
      @Functor.CommShift.comp _ _ _ _ _ _ (J E) V ℤ _ _ _ _ inferInstance s = c E := by
    apply commShift_ext
    intro n
    change precompShift (J E) V n (e n) = (c E).commShiftIso n
    exact he E n
  exact @compatibility_transport _ _ _ _ _ _ _ _ cA _ _ hc' _ hc

end WeilConjectures.CoefQbarVerdier
