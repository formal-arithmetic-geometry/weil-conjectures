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
public import Mathlib.RingTheory.FiniteType
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleAlgebraStage
import WeilConjectures.AlgebraicGeometry.ProperClosedFibreApproximation

/-!
# Finite-type descent of a finite étale closed-fibre cover

## References

* Stacks Project, Tags 0GS2, 0A0P, 01ZM, 01ZO and 07RP
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A closed-fibre cover descends to a proper scheme over a finite-type integer ring.
No henselian hypothesis or henselization is used in this statement
(Stacks, Tag 0GS2, General case). -/
theorem exists_finiteEtale_finiteType_closedFibre_stage
    {A : Type u} [CommRing A] (I : Ideal A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R)
      (α : R →+* A) (X : Scheme.{u}) (h : X ⟶ Spec (.of R)) (_ : IsProper h)
      (p : Y ⟶ X),
      p ≫ h = f ≫ Spec.map (CommRingCat.ofHom α) ∧
      ∃ (q : pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
        pullback h (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I.comap α)))))
        (U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
          (pullback h (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.comap α)))))),
        pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ p =
          q ≫ pullback.fst h (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.comap α)))) ∧
        q ≫ pullback.snd h (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I.comap α)))) =
          pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
            Spec.map (CommRingCat.ofHom (Ideal.quotientMap I α le_rfl)) ∧
        Nonempty (Over.mk (pullback.snd U.hom q) ≅ Over.mk V.hom) := by
  classical
  obtain ⟨Λ, hpre, hne, hdir, D, π, ⟨hc⟩, htrans, hcompact, hqs, hstage⟩ :=
    exists_proper_closedFibre_approximation I f
  let := hpre
  let := hne
  let := hdir
  let : ∀ {i j : Λᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := htrans
  let : ∀ i, CompactSpace (D.obj i) := hcompact
  let : ∀ i, QuasiSeparatedSpace (D.obj i) := hqs
  have : IsFinite V.hom := V.prop.1
  have : Etale V.hom := V.prop.2
  obtain ⟨i, W, g, hfin, het, v, H⟩ :=
    exists_finiteEtale_limit_stage D (Cone.mk _ π) hc V.hom
  obtain ⟨R, hR, hft, α, X, h, hproper, p, e, hp, hfst, hsnd⟩ :=
    hstage (Opposite.op i)
  let := hR
  have := hft
  have := hproper
  have := hfin
  have := het
  let q := π.app (Opposite.op i) ≫ e.hom
  let U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback h (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.comap α))))) :=
    MorphismProperty.Over.mk _ (g ≫ e.hom) ⟨inferInstance, inferInstance⟩
  have H' : IsPullback v V.hom U.hom q := by
    apply H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e <;> simp [U, q]
  refine ⟨R, hR, hft, α, X, h, hproper, p, hp, q, U, hfst, hsnd, ?_⟩
  refine ⟨Over.isoMk H'.isoPullback.symm ?_⟩
  exact H'.isoPullback_inv_snd


end AlgebraicGeometry.Scheme
