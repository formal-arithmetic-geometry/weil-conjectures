/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Paper.DifferenceFirstInputRestriction
public import Sheaf.Paper.PurityDiagonalSectionPasting
public import Sheaf.Paper.FiniteTypeExceptionalInverseImage

/-! # Agreement of the two normalized exceptional locality presentations

Source: composition coherence Step 1, counit-normalized etale locality.
(blueprint: lem-pur-normalized-etale-restriction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The exceptional-compositor/rho expression for E agrees with the uniquely
counit-normalized ambient locality expression, including structure-map congruence.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1;
lem-pur-diagonal-section-pasting, proof Steps 10--11.
(blueprint: lem-pur-normalized-etale-restriction-comparison).

Proof: eliminate hv, so the structure-map congruences on both sides are the
identity. Before evaluation at the coefficient unit, the inverse ambient locality
map is the right mate of compact-support composition followed by the normalized
proper-support/sum comparison. Conjugacy of a composite reverses composition.
Consequently this right mate is exceptional composition followed by rho. The
rho used by FiniteEtaleNormalization is the unique right mate of the same
graph-normalized support comparison: its normalization theorem identifies that
comparison with the canonical proper/open comparison. Thus the two natural
isomorphisms have the identical counit transpose. Injectivity of adjunction's
hom equivalence proves equality. Evaluate at the coefficient unit and insert
the exact-to-derived pullback constraint; this yields the displayed equality.
Transport back along hv. No section, coordinate, tensor product, or smoothness
is used, and the same argument applies to the empty scheme. -/
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
        DiagonalPasting.etaleRestriction P.Coefficient P v h := by sorry

end WeilConjectures.PurityFiniteSetting
