/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.SixFunctors.Coef.CoefIntegralFiniteExtension
import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralHomTensorPresentation
import all WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionHomMapInvertibility

/-! # Joint normalized scalar Hom presentations

Source: current blueprint, fix-prop-coherence.proof.md, evaluation sentence;
lem-sf-general-hom-comparison-cocycles, proof step 5.
(blueprint: lem-sf-scalar-hom-presentation-evaluation).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Simultaneous comparison of the ordinary scalar tensor-Hom and completion models.
The first equality is an ordinary Hom square; completion is imposed only in the
second equation, before requiring any input to be complete.

Source: current blueprint fix-prop-coherence.proof.md, general Hom sentence;
lem-sf-general-hom-comparison-cocycles, step 5; Stacks 07A4, 08J9 and
Bhatt--Scholze 3.5.1 for the fixed completed-scalar comparison.
(blueprint: lem-sf-scalar-hom-presentation-evaluation).

Proof:
1. The two completed coefficient maps agree on every finite projection, hence agree
by the inverse-limit property. Their ordinary scalar functors have the same balanced
sectionwise tensor model. The universal left-derived comparisons therefore give a
natural isomorphism e from pbcDerivedExtend to integralOrdinaryDerivedScalar,
normalized by those ordinary tensor units.
2. Choose source and target TensorPresentation by transporting the fixed natural
closed adjunctions along Koszul symmetry, on every ambient input. Their signed
Hom-complex evaluation and total-tensor comparison supply all presentation fields.
The ordinary scalar tensor comparisons agree on each pure-tensor generator, and
hence on all representatives by sheafification and tensor universality. Descend the
square by the universal K-flat comparison. Transposing it with the specified
adjunctions gives the first equality, with e inverse in the contravariant input.
3. Both completion transformations have the same finite quotient components
x maps to 1 tensor x and zero shifted coordinate in the Roos cocone. The two
coordinate projections determine the cocone map. After the ordinary comparison e,
the representative maps therefore agree. The uniqueness in normalized localization
descent proves the second equation on every ambient K. No completeness hypothesis
is used in these equations, no arbitrary presentation is substituted, and the
identity extension, ramification, zero inputs and unbounded inputs are included. -/
theorem scalarHom_presentation_evaluation
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :
    ∃ (a : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (b : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l L X))
      (e : pbcDerivedExtend (completedCoefficientMap l E L ι X) ≅
        integralOrdinaryDerivedScalar l E L ι X),
      (∀ K M : DerivedCategory (scalarReductionSource l E X),
        IntegralFiniteExtension.homMap X (completedCoefficientMap l E L ι X) a b K M ≫
            (coefficientIntegralInternalHom l L X).map
              (Prod.mkHom (e.inv.app K).op (e.hom.app M)) =
          e.hom.app ((coefficientIntegralInternalHom l E X).obj (op K, M)) ≫
            scalarHomOrdinary l E L ι X K M) ∧
      ∀ K : DerivedCategory (scalarReductionSource l E X),
        (completedScalarComparison l E L ι X).app K =
          e.hom.app K ≫ (scalarCompletion l E L ι X).app K := by
  classical
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  obtain ⟨a⟩ := IntegralHom.tensor_presentation_exists l E X D hl
  obtain ⟨b⟩ := IntegralHom.tensor_presentation_exists l L X D hl
  obtain ⟨t, e, ht, he, hχ⟩ := integralScalarOrdinaryModelComparison l E L ι X
  let G := pbcDerivedExtend (completedCoefficientMap l E L ι X)
  let eG : integralOrdinaryDerivedScalar l E L ι X ≅ G := e
  refine ⟨a, b, eG.symm, ?_, ?_⟩
  · intro K M
    let SA := scalarIntegralClosed l E X
    let SB := scalarIntegralClosed l L X
    let μ := IntegralFiniteExtension.transportTensor SA SB eG (scalarClosedTensor l E L ι X)
    let μa := PurCompactSupport.scalarTensor (completedCoefficientMap l E L ι X)
      (IntegralFiniteExtension.tensorModel X a) (IntegralFiniteExtension.tensorModel X b)
    let H := (IntegralHom.hom.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M)
    let γa := Adjunction.leftAdjointUniq (a.adjunction K) (SA.adjunction K)
    let γb := Adjunction.leftAdjointUniq (b.adjunction (G.obj K)) (SB.adjunction (G.obj K))
    have hn := IntegralFiniteExtension.scalarTensor_model_comparison
      l E L ι X a b t e ht he
    have hs : μa.inv.app (K, H) ≫ G.map (γa.hom.app H) =
        γb.hom.app (G.obj H) ≫ μ.inv.app (H, K) := by
      exact IntegralFiniteExtension.inverseSquare (μa.app (K, H)) (μ.app (H, K))
        (G.map (γa.hom.app H)) (γb.hom.app (G.obj H)) (hn K H)
    have hc : IntegralFiniteExtension.homMap X (completedCoefficientMap l E L ι X) a b K M =
        coefficientBaseChangeHom SA SB G μ K M := by
      exact IntegralFiniteExtension.transposeComparison (a.adjunction K) (SA.adjunction K)
        (b.adjunction (G.obj K)) (SB.adjunction (G.obj K)) G M
        (μa.inv.app (K, H)) (μ.inv.app (H, K)) hs
    rw [hc, IntegralFiniteExtension.transportHom SA SB eG]
    change (eG.inv.app H ≫ scalarHomOrdinary l E L ι X K M ≫
      (coefficientIntegralInternalHom l L X).map
        (Prod.mkHom (eG.inv.app K).op (eG.hom.app M))) ≫
      (coefficientIntegralInternalHom l L X).map
        (Prod.mkHom (eG.hom.app K).op (eG.inv.app M)) =
      eG.inv.app H ≫ scalarHomOrdinary l E L ι X K M
    simp only [Category.assoc, ← Functor.map_comp, prod_comp, ← op_comp,
      Iso.hom_inv_id_app, op_id, ← prod_id]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  · intro K
    apply (cancel_epi (eG.hom.app K)).1
    change e.hom.app K ≫ (completedScalarComparison l E L ι X).app K =
      e.hom.app K ≫ e.inv.app K ≫ (scalarCompletion l E L ι X).app K
    rw [Iso.hom_inv_id_app_assoc]
    exact NatTrans.congr_app hχ K

end WeilConjectures
