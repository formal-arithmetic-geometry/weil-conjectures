/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.DualBaseChangeFiniteStage
public import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum

/-! Naturality and invertibility of the normalized higher compact exchange. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.SuppliedExchangeProjection
namespace WeilConjectures

/-- The normalized compact exchange has a coherent restricted isomorphism family.

The proof is the componentwise A2 argument: use the compact-exchange isomorphism on the
finite-Tor (or unrestricted) domain, transport it through the two normalization isomorphisms,
and use full faithfulness of the restricted inclusion to lift the resulting natural
transformation.  The componentwise construction gives the naturality equation required by
`NatIso.ofComponents`; this is exactly fix-lem-exchanges (1), for the normalized datum.
Source: blueprint `fix-lem-exchanges` (1), applied to the normalized compact exchange.
(blueprint: fix-lem-exchanges)
(blueprint: lem-sf-dual-base-change-higher-exchange-naturality)
-/
theorem dualBaseChangeHigherExchangeNaturality
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X, Category.{w} (B X)] {S : SixFunctorPushStage D B}
    {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {P : ∀ X, ObjectProperty (B X)} (H : SixFunctorCoherentStage S P)
    (hA : SixFunctorExchangeAxioms A P) :
    ∃ τ : DualBaseChangeExchangeFamily S H,
      ∀ (Q : SixFunctorCompactifiedSquare D) [DualBaseChangeAdmissible Q],
        (τ Q).hom = dualBaseChangeExchange S H Q
          (dualBaseChangeHigherExchange (A Q))  := by
  let τ : DualBaseChangeExchangeFamily S H := fun Q (_ : DualBaseChangeAdmissible Q) ↦ by
    let e := dualBaseChangeExchange S H Q (dualBaseChangeHigherExchange (A Q))
    haveI : ∀ K, IsIso (e.app K) := fun K ↦ by
      haveI : IsIso ((dualBaseChangeHigherExchange (A Q)).app K.obj) := by
        dsimp [dualBaseChangeHigherExchange]
        haveI := hA.compactExchange Q K.obj K.property
        infer_instance
      haveI : IsIso ((Functor.whiskerLeft (P Q.X).ι
          (dualBaseChangeHigherExchange (A Q))).app K) := by
        change IsIso ((dualBaseChangeHigherExchange (A Q)).app K.obj)
        infer_instance
      haveI : IsIso ((P Q.Y').ι.map (e.app K)) := by
        change IsIso ((Functor.whiskerLeft (P Q.X).ι
          (dualBaseChangeHigherExchange (A Q))).app K)
        infer_instance
      exact (P Q.Y').fullyFaithfulι.isIso_of_isIso_map (e.app K)
    exact NatIso.ofComponents (fun K ↦ asIso (e.app K)) (fun f ↦ by
      apply (P Q.Y').fullyFaithfulι.map_injective
      change
        (S.pull Q.g).map ((S.support Q.f Q.compactification).map f.hom) ≫
            (dualBaseChangeHigherExchange (A Q)).app _ =
          (dualBaseChangeHigherExchange (A Q)).app _ ≫
            (S.support Q.f' Q.compactification').map ((S.pull Q.g').map f.hom)
      simpa only [Functor.comp_map, Functor.whiskerLeft_app, Functor.whiskerRight_app] using
        (dualBaseChangeHigherExchange (A Q)).naturality f.hom)
  refine ⟨τ, ?_⟩
  intro Q _
  ext K
  rfl

end WeilConjectures
