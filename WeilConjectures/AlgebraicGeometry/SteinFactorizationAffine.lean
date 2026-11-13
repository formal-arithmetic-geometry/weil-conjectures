/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperNormalizedFibres
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections

/-!
# Stein factorization over an affine base

## References

* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a proper `f` over `Spec A`, put `B = Γ(X, ⊤)`. The ring map `A → B` is integral, the
map `X.toSpecΓ : X ⟶ Spec B` is proper with geometrically connected fibres, and each fibre and
each topological inverse image of a point of `Spec B` is connected (thus nonempty). -/
theorem Scheme.Hom.steinFactorization_affine {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom.IsIntegral ∧
      IsProper X.toSpecΓ ∧ GeometricallyConnected X.toSpecΓ ∧
      ∀ t : Spec Γ(X, ⊤), ConnectedSpace (X.toSpecΓ.fiber t) ∧
        _root_.IsConnected (X.toSpecΓ ⁻¹' {t}) := by
  -- Integrality and properness follow directly from Mathlib.
  have hi : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  have : IsProper (X.toSpecΓ ≫ f.steinFactorizationBase) := by simpa
  have : IsProper X.toSpecΓ := IsProper.of_comp X.toSpecΓ f.steinFactorizationBase
  have : IsIso X.toSpecΓ.appTop := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace X.toSpecΓ
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated X.toSpecΓ
  have : GeometricallyConnected X.toSpecΓ := by
    rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
    intro s
    apply (X.toSpecΓ.geometricallyConnected_fiber_iff_connectedSpace_etale_neighbourhood s).2
    intro U e _ t _ht
    -- Work over an affine open neighbourhood of the étale point.
    obtain ⟨R, j, hj, v, hv⟩ := Scheme.exists_Spec_apply_eq t
    have : IsOpenImmersion j := hj
    let e' := j ≫ e
    let p := Limits.pullback.snd X.toSpecΓ e'
    have : Flat e' := inferInstance
    have hp := isPushout_appTop_of_flat e' X.toSpecΓ
    have : IsIso p.appTop := hp.isIso_inr_of_isIso
    have : IsIso ((Scheme.ΓSpecIso R).inv ≫ p.appTop) := inferInstance
    have : IsProper p := inferInstance
    have hc : ConnectedSpace (p.fiber v) :=
      p.connectedSpace_fiber_of_isProper_of_globalSections_iso v
    -- An open immersion induces an isomorphism on the corresponding fibres.
    let a : Limits.pullback X.toSpecΓ e' ⟶ Limits.pullback X.toSpecΓ e :=
      Limits.pullback.lift (Limits.pullback.fst X.toSpecΓ e') (p ≫ j) (by
        simp only [Category.assoc, e', p, Limits.pullback.condition])
    have hsquare : IsPullback a p (Limits.pullback.snd X.toSpecΓ e) j := by
      apply IsPullback.of_right (h₁₂ := Limits.pullback.fst X.toSpecΓ e)
      · simpa [a, p, e'] using IsPullback.of_hasPullback X.toSpecΓ e'
      · simp [a]
      · exact IsPullback.of_hasPullback X.toSpecΓ e
    have hf := isPullback_fiberToSpecResidueField_of_isPullback hsquare v
    have := hf.isIso_fst_of_isIso
    have hc' : ConnectedSpace ((Limits.pullback.snd X.toSpecΓ e).fiber (j v)) := by
      let b := Limits.pullback.map p ((Spec R).fromSpecResidueField v)
        (Limits.pullback.snd X.toSpecΓ e) (U.fromSpecResidueField (j v))
        a (Spec.map (j.residueFieldMap v)) j
        hsquare.w.symm (by simp)
      exact b.homeomorph.connectedSpace_iff.mp hc
    change j v = t at hv
    rw [hv] at hc'
    exact hc'
  refine ⟨hi, inferInstance, inferInstance, ?_⟩
  intro t
  exact ⟨inferInstance, Scheme.Hom.isConnected_preimage_singleton X.toSpecΓ t⟩

end AlgebraicGeometry
