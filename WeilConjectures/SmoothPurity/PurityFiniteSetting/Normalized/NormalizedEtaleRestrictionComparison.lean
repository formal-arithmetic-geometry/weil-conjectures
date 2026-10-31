/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DifferenceCoordinateSection.DifferenceFirstInputRestriction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPasting
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteTypeExceptionalInverseImage
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws

/-! # Agreement of the two normalized exceptional locality presentations

Source: composition coherence Step 1, counit-normalized etale locality.
(blueprint: lem-route-normalized-e-eq-etale-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem choose_unique_eq_choose_exists {α : Sort*} {p : α → Prop}
    (H : ∃! x, p x) : Classical.choose H = Classical.choose H.exists :=
  ((Classical.choose_spec H).2 _ (Classical.choose_spec H.exists)).symm

/-- The exceptional-compositor/rho expression for E agrees with the uniquely
counit-normalized ambient locality expression, including structure-map congruence.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1;
compatibility with etale localization.
(blueprint: lem-route-normalized-e-eq-etale-restriction).

Proof: eliminate hv and give the three schemes their finite-type field structures.
The existing sourceEtale_locality_congr calculation identifies the normalized
exceptional-compositor/rho expression with the inverse structural locality map.
The latter selects its isomorphism directly from a unique-existence theorem,
whereas etaleRestriction selects from its existence consequence. Uniqueness
identifies the two choices. Unfold restrictionUnit and structural locality, and
reverse composition to obtain etaleRestriction. This adds no absolute separatedness
hypothesis and also applies to the empty scheme. -/
theorem normalizedE_eq_etaleRestriction (P : PurityFiniteSetting.{u})
    {W X B : Scheme.{u}} (v : W ⟶ X) (h : X ⟶ B) (q : W ⟶ B)
    [Etale v] [IsSeparated v] [QuasiCompact v]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    [HasCompactification h] [HasCompactification q]
    (hv : q = v ≫ h) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] :
    letI := P.noetherian aB
    letI := P.noetherian (h ≫ aB)
    letI := P.noetherian (q ≫ aB)
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    letI : HasCompactification (v ≫ h) := HasCompactification.of_eq hv
    ProEtale.DifferenceCoordinateSection.normalizedE P v h q hv aB =
      DiagonalPasting.dualizingCongr P.Coefficient P hv ≪≫
        DiagonalPasting.etaleRestriction P.Coefficient P v h := by
  subst q
  let : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  let : X.Over (Spec (.of P.field.k)) := ⟨h ≫ aB⟩
  let : W.Over (Spec (.of P.field.k)) := ⟨(v ≫ h) ≫ aB⟩
  let : v.IsOver (Spec (.of P.field.k)) := ⟨(Category.assoc v h aB).symm⟩
  let : h.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : (v ≫ h).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  let : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  let : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (h ≫ aB))
  let : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (h ≫ aB))
  let : LocallyOfFiniteType (W ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType ((v ≫ h) ≫ aB))
  let : QuasiCompact (W ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact ((v ≫ h) ≫ aB))
  have hs := SectionRestriction.sourceEtale_locality_congr P v h (v ≫ h) rfl
  simpa only [ProEtale.DifferenceCoordinateSection.normalizedE,
    DiagonalPasting.etaleRestriction, DiagonalPasting.dualizingCongr,
    ProEtale.FiniteEtaleNormalization.coefficientUnit, Iso.refl_trans,
    Etale.sectionStructuralLocalityIso, DiagonalPasting.restrictionUnit,
    Iso.trans_symm, choose_unique_eq_choose_exists] using hs

end WeilConjectures.PurityFiniteSetting
