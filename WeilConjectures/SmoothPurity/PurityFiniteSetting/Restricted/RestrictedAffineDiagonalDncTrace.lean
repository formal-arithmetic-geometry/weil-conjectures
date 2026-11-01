/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.RestrictedAffineDiagonalSectionTrace
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Restricted.RestrictedAffineDiagonalVectorIntegration

/-! # DNC and integration on the affine diagonal

Source: smooth-purity, Agreement on the model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Integration on the diagonal section, followed by DNC and normal-section purity,
is the identity of the local Tate object. This statement involves neither alpha nor
rho, and the integration is taken over the local source scheme p inverse V.
Source: smooth-purity Agreement on the model, translation and standard-pair paragraphs;
diagonal-dualizing-object proof Steps 1--2.
(blueprint: lem-pur-restricted-affine-diagonal-dnc-trace).

Proof: the geometric DNC coordinate theorem constructs a common vector presentation
of the diagonal and normal pairs. Write cS and cN for the actual section exchanges
from source and normal to that vector presentation. Its equation is delta followed
by normalComparison and nu*(cN) equals sourceComparison followed by nu*(cS).
The integration theorem identifies the local trace followed by sourceComparison
and nu*(cS) with nu*(vectorBetaInverse). The chart's normalized field identifies
betaEtale inverse followed by cN with the same vectorBetaInverse. Apply nu* to
this normalization equation. Precompose the geometric equation by the local trace
and substitute these two integration equations. Cancel nu*(cN), which is an
isomorphism. The resulting trace-delta-normalComparison composite is nu* of
betaEtale inverse. By the definition of beta, the desired identity now follows
from functoriality and betaEtale inverse followed by betaEtale hom. The geometric
and integration statements include empty schemes and rank zero, and retain every
normalized t and D. -/
theorem restrictedAffineDiagonalDncTrace (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    [SmoothOfRelativeDimension d (affineTraceProjection Y d)]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (E : OrientationRefinement.Chart P (affineTraceProjection Y d) aY d V)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    OrientationCounit.restrictedAffineDiagonalSectionTrace P Y d aY V E.geometry t D ≫
        (OrientationRefinement.delta P (affineTraceProjection Y d) aY d V E.geometry).hom ≫
        (OrientationRefinement.beta P (affineTraceProjection Y d) aY d V
          E.geometry E.betaEtale).hom =
      𝟙 (P.diagonalTwist (affineTraceProjection Y d ⁻¹ᵁ V.1).toScheme d) := by
  let H := E.geometry
  let := H.separated
  let := H.finiteType
  let := H.quasiCompact
  let := H.smoothDimension
  let := H.baseFiniteType
  let := H.baseQuasiCompact
  let := H.sourceSeparated
  let := H.sourceFiniteType
  let := H.sourceQuasiCompact
  let h := affineTraceProjection Y d ∣_ V.1
  let B := (affineTraceProjection Y d ⁻¹ᵁ V.1).toScheme
  let aB := h ≫ V.1.ι ≫ aY
  let := P.noetherian aB
  let := SmoothOfRelativeDimension.smooth d h
  let g := pullback.fst h h
  let s := pullback.diagonal h
  let := Dnc.compactifiable P g aB
  let := Dnc.invertibleExponent P (g ≫ aB)
  let q := Scheme.Hom.normalConeProj g s
  let := Dnc.normalCompactifiable P d g aB s (pullback.diagonal_fst h)
  let : SmoothOfRelativeDimension d q :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst h)).smoothOfRelativeDimension_proj
  let := Dnc.invertibleExponent P (q ≫ aB)
  obtain ⟨F, hF, n, w, hz, e, we, ze, hd⟩ :=
    P.restrictedAffineDiagonalDncVectorCoordinates Y d aY V H
  let := hF
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  let cN := vectorModelSectionComparison P.Coefficient d q s.normalConeZeroSection F n w hz
  let cS := vectorModelSectionComparison P.Coefficient d g s F e we ze
  let δ := OrientationRefinement.delta P (affineTraceProjection Y d) aY d V H
  let sc := Dnc.sourceComparison P d g aB s
  let nc := Dnc.normalComparison P d g aB s (pullback.diagonal_fst h)
  let S := OrientationCounit.restrictedAffineDiagonalSectionTrace P Y d aY V H t D
  have hd' : δ.hom ≫ nc.hom ≫ ν.map cN.hom = sc.hom ≫ ν.map cS.hom := hd
  have hi : S ≫ sc.hom ≫ ν.map cS.hom =
      ν.map (OrientationRefinement.vectorBetaInverse P B aB d F) :=
    P.restrictedAffineDiagonalVectorIntegration Y d aY V H t D F e we ze
  have hn : E.betaEtale.inv ≫ cN.hom =
      OrientationRefinement.vectorBetaInverse P B aB d F := E.normalized F n w hz
  have heq : S ≫ δ.hom ≫ nc.hom = ν.map E.betaEtale.inv := by
    apply (cancel_mono (ν.map cN.hom)).1
    calc
      (S ≫ δ.hom ≫ nc.hom) ≫ ν.map cN.hom =
          S ≫ sc.hom ≫ ν.map cS.hom := by
        simpa only [Category.assoc] using congrArg (fun k ↦ S ≫ k) hd'
      _ = ν.map (OrientationRefinement.vectorBetaInverse P B aB d F) := hi
      _ = ν.map E.betaEtale.inv ≫ ν.map cN.hom := by rw [← hn, Functor.map_comp]
  change S ≫ δ.hom ≫ (nc ≪≫ ν.mapIso E.betaEtale).hom = _
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  calc
    _ = (S ≫ δ.hom ≫ nc.hom) ≫ ν.map E.betaEtale.hom := by
      simp only [Category.assoc]
    _ = ν.map E.betaEtale.inv ≫ ν.map E.betaEtale.hom := by rw [heq]
    _ = _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id]
      exact ν.map_id _

end WeilConjectures.PurityFiniteSetting
