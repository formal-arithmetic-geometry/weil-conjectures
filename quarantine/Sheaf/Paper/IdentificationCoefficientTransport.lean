/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.IdentityCoefficientTransportData

import Sheaf.Paper.FiniteIdentityCompositionNormalization
import Sheaf.Paper.HigherIdentityCompositionNormalization

/-! # Identity-point coefficient transport

Source: blueprint main-20261015, `sk-thm-sf-identification.proof.md`, normalized
trace at the point; `fix-lem-exchanges`, clauses (2) and (4)
(blueprint: lem-sf-identification-coefficient-transport).

## Main declarations

- `sfIdentityComposition`: the datum's specified compositor with the identity.
- `sfIdentityNormalizedCounit`: the identity-normalized counit nu.
- `sfIdentityTransportMate`: the conjugate of the inverse compositor.
- `SfIdentityStageLaws`: the displayed equations at one coefficient stage.
- `SfIdentityChange`: transport through the specified coefficient comparisons.
- `sfFiniteIdentityComparison`: the finite identity-compactification comparison.
- `identificationCoefficientTransport`: normalization at all four coefficient stages.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w v₁ w₁
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

private theorem identity_mate_formula
    {A : Type v} {B : Type w} [Category A] [Category B]
    {F : A ⥤ B} {G : B ⥤ A} {I J : B ⥤ B}
    (a : F ⊣ G) (b : I ⊣ J) (v : I ≅ 𝟭 B)
    (α : F ⋙ I ≅ F)
    (hα : ∀ K, α.hom.app K = v.hom.app (F.obj K)) (L : B) :
    (conjugateIsoEquiv (a.comp b) a α.symm).hom.app L =
      G.map (v.inv.app (J.obj L) ≫ b.counit.app L) := by
  have hinv (K : A) : α.inv.app K = v.inv.app (F.obj K) := by
    apply (cancel_mono (v.hom.app (F.obj K))).1
    calc
      α.inv.app K ≫ v.hom.app (F.obj K) =
          α.inv.app K ≫ α.hom.app K := by rw [hα K]
      _ = 𝟙 _ := α.inv_hom_id_app K
      _ = v.inv.app (F.obj K) ≫ v.hom.app (F.obj K) :=
        (v.inv_hom_id_app (F.obj K)).symm
  rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  simp only [Iso.symm_hom, Adjunction.comp_counit_app, Functor.comp_obj,
    Functor.map_comp, hinv]
  have hv := v.inv.naturality (a.counit.app (J.obj L))
  simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hv
  rw [← G.map_comp_assoc, ← hv, G.map_comp]
  simp only [Category.assoc]
  rw [a.right_triangle_components_assoc]

private theorem identity_stage_laws
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (P : ∀ X, B X → Prop)
    (L : B (sixFunctorPoint D))
    (v : S.support (𝟙 (sixFunctorPoint D))
      (sfPointIdentityCompactification D) ≅ 𝟭 _)
    (h : SfIdentityCompositionLaw S v) :
    SfIdentityStageLaws S P L v := by
  have hν : (conjugateIsoEquiv
      (S.exceptionalAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)) Adjunction.id v.symm).hom.app L =
      sfIdentityNormalizedCounit S L v := by
    simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom,
      conjugateEquiv_adjunction_id, sfIdentityNormalizedCounit]
  have hmate (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
      (c : Compactification (sixFunctorStructure X).hom.left) :
      (sfIdentityTransportMate S X c).hom.app L =
        (S.exceptional (sixFunctorStructure X) c).map
          (sfIdentityNormalizedCounit S L v) :=
    identity_mate_formula (S.exceptionalAdjunction (sixFunctorStructure X) c)
      (S.exceptionalAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)) v (sfIdentityComposition S X c)
      (h X c) L
  refine ⟨fun X _ c K _ ↦ h X c K, ?_, ?_, hmate, ?_⟩
  · rw [← hν]
    infer_instance
  · intro X _ c
    infer_instance
  · intro X _ c
    rw [hmate X c]
    exact (S.exceptionalAdjunction (sixFunctorStructure X) c).counit.naturality
      (sfIdentityNormalizedCounit S L v)

/-- The coefficient-stage transport statement, including finite, completed integral,
rational and common finite-stage coefficients.
Source: blueprint main-20261015, `sk-thm-sf-identification.proof.md`, normalized trace
(blueprint: lem-sf-identification-coefficient-transport).

Proof:
1. The identity clause of thm-sf-comp-composition computes the finite compositor.
   Integrally, the identity compactification is reduction followed by total limit.
   The identity-open case of lem-sf-integral-open-reduction-comparison fixes its
   comparison as the inverse actual unit of lem-coef-derived-system-evaluation-calculus.
   The reduction equations below characterize this same inverse on the point category;
   they use the datum's projection-normalized reduction comparisons.
2. Write a = p j and apply lem-sf-integral-compactification-comparison-bridge to
   the strict semilinear system S_p J_j of finite reductions. The finite-Tor bounds,
   compatible origins and A5 put it in the domain of
   lem-sf-integral-compactification-system-realization. Retain the identity outer
   compactification and the same compactification for the composite.
3. By lem-sf-ambient-proper-open-pasting its system proper/open comparison is identity.
   The bridge identifies the specified completed compositor of fix-lem-exchanges (2),(4)
   with C L(e_N) L R(C inverse). Naturality of the actual reconstruction unit u and
   the triangle L(e_N) u_(L N) = 1 give alpha u = 1, hence alpha = u inverse.
4. Apply raw scalar localization, whose morphisms are fractions, to this equality.
   Naturality holds on numerators and denominators. At algebraically closed coefficients,
   represent all objects and arrows at one common finite coefficient field and pass
   the equality through the supplied A5 coefficient comparisons.
5. Conjugate v inverse for I adjoint to J and the identity adjunction. The component
   formula of def-weil-pbc-adjunction-conjugate is e_L v_(J L) inverse, so nu is invertible.
6. For F adjoint to G, the composite adjunction counit is e_L I(mu_(J L)), as in
   def-weil-pbc-composite-adjunction. Substitute alpha = v F into its conjugate formula.
   Naturality of v inverse moves it past mu; the F-G triangle cancels the remaining
   unit and counit. The result is c_L = G(e_L v_(J L) inverse), giving c = G(nu)
   and invertibility of c.
7. Naturality of the exceptional counit at nu gives the displayed counit equation. -/
theorem identificationCoefficientTransport
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) :
    (@SfIdentityStageLaws.{u, u+2, u+2} D
      (sixFunctorFiniteCategory D C E n hn)
      (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
      S.finite S.toSixFunctorOperationDatum.finiteTorDomain
      (@SixFunctorDualityData.unit.{u, u+2, u+2} D
        (sixFunctorFiniteCategory D C E n hn)
        (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
        S.finite (sixFunctorFiniteHomPairs D C E n hn) S.finiteDuality)
      (sfFiniteIdentityComparison D C E n hn S.toSixFunctorFiniteOperations)) ∧
    (∃ vI : S.higher.integral.support (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityStageLaws S.higher.integral
        S.toSixFunctorOperationDatum.integralFiniteTorDomain
        S.higher.integralDuality.unit vI ∧
    ∃ vR : S.higher.rational.support (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityStageLaws S.higher.rational (fun _ ↦ ⊤)
        S.higher.rationalDuality.unit vR ∧
      SfIdentityChange S.higher.rationalization vI vR ∧
      (∀ m : ℕ, @SfIdentityChange.{u, u+2, u+2, u+2, u+2} D
        (fun X ↦ sfIntegralConstructibleCategory C.l E X.obj.left)
        (fun X ↦ inferInstanceAs (Category.{u+2}
          (sfIntegralConstructibleCategory C.l E X.obj.left)))
        (sixFunctorFiniteCategory D C E (m+1) (Nat.succ_le_succ (Nat.zero_le m)))
        (fun X ↦ inferInstanceAs (Category.{u+2}
          (sixFunctorFiniteCategory D C E (m+1) (Nat.succ_le_succ (Nat.zero_le m)) X)))
        _ _ _ (S.integralNormalization.reduction m) vI
        (sfFiniteIdentityComparison D C E (m+1) (Nat.succ_le_succ (Nat.zero_le m))
          (S.integralNormalization.finiteLevels m))) ∧
    ∃ vQ : S.closure.commonStage.support (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityStageLaws S.closure.commonStage (fun _ ↦ ⊤)
        S.closure.commonStageDuality.unit vQ ∧
    ∀ L : Padic.FiniteCoefficientFields C.l C.Qbar,
      ∃ vLI : (S.closure.coefficientStages L).integral.support
          (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _,
      ∃ vLR : (S.closure.coefficientStages L).rational.support
          (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityStageLaws (S.closure.coefficientStages L).integral
          (fun X K ↦ finiteTorConstructibleIntegral C.l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left K.obj)
          (S.closure.coefficientStages L).integralDuality.unit vLI ∧
      SfIdentityStageLaws (S.closure.coefficientStages L).rational (fun _ ↦ ⊤)
          (S.closure.coefficientStages L).rationalDuality.unit vLR ∧
      SfIdentityChange (S.closure.coefficientStages L).rationalization vLI vLR ∧
      SfIdentityChange (S.closure.commonStageComparison L) vLR vQ ∧
      ∀ m : ℕ, @SfIdentityChange.{u, u+2, u+2, u+2, u+2} D
        (fun X ↦ sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left)
        (fun X ↦ inferInstanceAs (Category.{u+2} (sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left)))
        (sixFunctorFiniteCategory D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L)
          (m+1) (Nat.succ_le_succ (Nat.zero_le m)))
        (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L)
          (m+1) (Nat.succ_le_succ (Nat.zero_le m)) X)))
        _ _ _ ((S.coefficientIntegralNormalization L).reduction m) vLI
        (sfFiniteIdentityComparison D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L)
          (m+1) (Nat.succ_le_succ (Nat.zero_le m))
          ((S.coefficientIntegralNormalization L).finiteLevels m))) := by
  obtain ⟨vI, hI, vR, hR, hIR, hred, vQ, hQ, hfields⟩ :=
    higherIdentityCompositionNormalization D C E n hn S
  refine ⟨identity_stage_laws _ _ _ _
    (finiteIdentityCompositionNormalization D C E n hn S.toSixFunctorFiniteOperations),
    vI, identity_stage_laws _ _ _ _ hI, vR,
    identity_stage_laws _ _ _ _ hR, hIR, hred, vQ,
    identity_stage_laws _ _ _ _ hQ, ?_⟩
  intro L
  obtain ⟨vLI, vLR, hLI, hLR, hILR, hLQ, hLred⟩ := hfields L
  exact ⟨vLI, vLR, identity_stage_laws _ _ _ _ hLI,
    identity_stage_laws _ _ _ _ hLR, hILR, hLQ, hLred⟩

end WeilConjectures
