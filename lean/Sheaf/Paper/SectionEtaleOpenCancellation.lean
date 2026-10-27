/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.Paper.PurityDiagonalSectionPasting

/-! # Open cancellation for normalized section locality

Source: composition coherence Step 1, compatible-chart source calculation.
(blueprint: lem-pur-section-etale-open-cancellation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Restricting both sides of an etale section comparison to an open containing
its section does not change the comparison.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1;
lem-pur-centred-diagonal-source-pasting, proof Step 1.
(blueprint: lem-pur-section-etale-open-cancellation).

Proof: the exceptional locality isomorphism is the right-adjoint mate of the
proper/open compact-support compositor followed by the normalized etale sum
comparison. Its defining counit equation uniquely determines it, independently
of N. Apply compact-support composition associativity to O -> W -> X -> B
and take right mates. After the derived/exact pullback comparisons this says
that locality for O -> X is locality for W -> X followed by that for O -> W,
with the pullback compositor inserted. Pull this identity to s'. The relation
s' O.ι = s identifies the composite pullback with pullback by s; s v = z
identifies the remaining composite with pullback by z. Pullback associativity
cancels their compositors. Inverting locality for O -> X then gives the
stated equality. The inverse full locality is exactly etaleSection, since its
chosen map satisfies the same counit equation. No Cartesian square for the
open is asserted. The proof uses neither a rank nor a nonempty scheme. -/
theorem sectionEtaleRestriction_open_cancel (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {W X B : Scheme.{u}} [IsNoetherian W] [IsNoetherian X] [IsNoetherian B]
    (v : W ⟶ X) [Etale v] [IsSeparated v] [QuasiCompact v]
    (h : X ⟶ B) (q : W ⟶ B) [HasCompactification h] [HasCompactification q]
    (hv : v ≫ h = q) (s : B ⟶ W) (z : B ⟶ X) (hz : s ≫ v = z)
    (O : W.Opens) (s' : B ⟶ O.toScheme) (hs : s' ≫ O.ι = s)
    [HasCompactification (O.ι ≫ q)] :
    letI : IsNoetherian O.toScheme := ⟨⟩
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    letI : HasCompactification (v ≫ h) := HasCompactification.of_eq hv.symm
    (P.chartSectionEtaleRestriction N O.ι q (O.ι ≫ q) rfl s s' hs) ≪≫
      (P.chartSectionEtaleRestriction N (O.ι ≫ v) h (O.ι ≫ q)
        (by rw [Category.assoc, hv]) z s'
        (by rw [← Category.assoc, hs, hz])).symm =
      DiagonalPasting.etaleSection P.Coefficient P v h q s z hv.symm hz.symm := by sorry

end WeilConjectures.PurityFiniteSetting
