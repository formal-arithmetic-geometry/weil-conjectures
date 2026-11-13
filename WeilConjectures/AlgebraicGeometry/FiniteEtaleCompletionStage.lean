/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteEtaleCompletionLift
import WeilConjectures.AlgebraicGeometry.FiniteEtaleAlgebraStage
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# A finite presentation stage for a cover of the closed fibre

## References

* Stacks Project, Tag 0GS2
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A closed-fibre cover has a finite étale model over a finitely presented algebra mapping
into the completion. No G-ring or henselian assumption is needed
(Stacks, Tag 0GS2). -/
theorem exists_finiteEtale_completion_stage
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R),
      Algebra.FinitePresentation A R ∧
      ∃ (c : R →ₐ[A] AdicCompletion I A)
        (W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A R)))))
        (k : pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
          pullback f (Spec.map (CommRingCat.ofHom (algebraMap A R)))),
        k ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A R))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ∧
        k ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A R))) =
          pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
            Spec.map (CommRingCat.ofHom
              ((AdicCompletion.evalOneₐ I).toRingHom.comp c.toRingHom)) ∧
        Nonempty (Over.mk (pullback.snd W.hom k) ≅ Over.mk V.hom) := by
  obtain ⟨U, j, hjfst, hjsnd, ⟨eU⟩⟩ := exists_finiteEtale_completion_lift I f V
  obtain ⟨R, hR, hAR, hfp, c, W, l, hlfst, hlsnd, ⟨eW⟩⟩ :=
    exists_finiteEtale_algebra_stage f U
  refine ⟨R, hR, hAR, hfp, c, W, j ≫ l, ?_, ?_, ?_⟩
  · rw [Category.assoc, hlfst, hjfst]
  · rw [Category.assoc, hlsnd, ← Category.assoc, hjsnd, Category.assoc,
      ← Spec.map_comp]
    rfl
  · exact ⟨(Over.pullbackComp j l).app (Over.mk W.hom) ≪≫
      (Over.pullback j).mapIso eW ≪≫ eU⟩

end AlgebraicGeometry.Scheme
