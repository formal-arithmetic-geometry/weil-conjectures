/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.FiniteEtaleCompletionStage
import WeilConjectures.RingTheory.HenselianApproximationAlgHom
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Finite étale lifting by henselian G-ring approximation

## References

* Stacks Project, Tag 0GS2
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every finite étale cover of the closed fibre of a proper scheme over a henselian G-ring
lifts to a finite étale cover of the scheme, with an isomorphism over the closed fibre
(Stacks, Tag 0GS2). -/
theorem exists_finiteEtale_lift_of_henselianPair_of_isGRing
    {A : Type u} [CommRing A] (hA : IsGRing A) (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y,
      Nonempty
        (Over.mk (pullback.snd U.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≅
          Over.mk V.hom) := by
  let : IsNoetherianRing A := hA.1
  obtain ⟨R, hR, hAR, hfp, c, W, k, hkfst, hksnd, ⟨e⟩⟩ :=
    exists_finiteEtale_completion_stage I f V
  let : CommRing R := hR
  let : Algebra A R := hAR
  let : Algebra.FinitePresentation A R := hfp
  obtain ⟨σ, hσ⟩ := exists_algHom_approximation_mod_ideal I hA c
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let b := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let s : Y ⟶ pullback f b := pullback.lift (𝟙 Y)
    (f ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      dsimp [b]
      rw [Category.id_comp, Category.assoc, ← Spec.map_comp]
      have hc : σ.toRingHom.comp (algebraMap A R) = RingHom.id A := by
        ext a
        exact σ.commutes a
      change f = f ≫ Spec.map (CommRingCat.ofHom (σ.toRingHom.comp (algebraMap A R)))
      rw [hc]
      simp)
  have hs : pullback.fst f q ≫ s = k := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, s, pullback.lift_fst, Category.comp_id] using hkfst.symm
    · simp only [Category.assoc, s, pullback.lift_snd]
      rw [← Category.assoc, pullback.condition, Category.assoc]
      dsimp [q]
      rw [← Spec.map_comp, hksnd]
      change _ ≫ Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk I).comp σ.toRingHom)) = _
      rw [hσ]
  have : IsFinite W.hom := W.prop.1
  have : Etale W.hom := W.prop.2
  let U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ (pullback.snd W.hom s) ⟨inferInstance, inferInstance⟩
  refine ⟨U, ⟨?_⟩⟩
  let a := pullbackLeftPullbackSndIso W.hom s (pullback.fst f q)
  let d : pullback W.hom (pullback.fst f q ≫ s) ≅ pullback W.hom k :=
    pullback.congrHom rfl hs
  refine Over.isoMk (a ≪≫ d) ?_ ≪≫ e
  dsimp [a, d]
  simp [U, q]
  rfl

end AlgebraicGeometry.Scheme
