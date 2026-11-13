/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.ProperLimitNoetherian
import WeilConjectures.AlgebraicGeometry.AffineApproximationRingPresentation
import WeilConjectures.AlgebraicGeometry.QuotientFibreLimitTransfer

/-!
# Closed fibres of proper Noetherian approximations

## References

* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
* [Stacks Project, Tag 0A0P](https://stacks.math.columbia.edu/tag/0A0P)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The closed fibre of a proper scheme is a directed limit of the closed fibres
of proper models over finite-type integer rings, with affine transitions
(Stacks, Tags 0GS2 and 0A0P). -/
theorem exists_proper_closedFibre_approximation
    {A : Type u} [CommRing A] (I : Ideal A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λᵒᵖ ⥤ Scheme.{u})
      (π : (Functor.const Λᵒᵖ).obj
        (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⟶ D),
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      (∀ {i j : Λᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)) ∧
      (∀ i, CompactSpace (D.obj i)) ∧ (∀ i, QuasiSeparatedSpace (D.obj i)) ∧
      ∀ i : Λᵒᵖ,
        ∃ (R : Type u) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R)
          (α : R →+* A) (X : Scheme.{u}) (h : X ⟶ Spec (.of R)) (_ : IsProper h)
          (p : Y ⟶ X)
          (e : D.obj i ≅ pullback h (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.comap α))))),
          p ≫ h = f ≫ Spec.map (CommRingCat.ofHom α) ∧
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ p =
            (π.app i ≫ e.hom) ≫ pullback.fst h (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I.comap α)))) ∧
          (π.app i ≫ e.hom) ≫ pullback.snd h (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.comap α)))) =
            pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
              Spec.map (CommRingCat.ofHom (Ideal.quotientMap I α le_rfl)) := by
  obtain ⟨Λ, hpre, hne, hdir, Xs, Ss, fs, p, s, hl, hs, ht, hp, hft, hw, ha⟩ :=
    AlgebraicGeometry.exists_proper_limit_noetherian f
  let _ : Preorder Λ := hpre
  let _ : Nonempty Λ := hne
  let _ : IsDirected Λ (· ≤ ·) := hdir
  obtain ⟨has, hcs⟩ := ha inferInstance
  obtain ⟨B, g, α, hc, hB, hg, hpg⟩ := affine_approximation_ring_presentation
    f Xs Ss fs p s (fun i ↦ (has i).1) (fun i ↦ (has i).2) hcs hp hw
  obtain ⟨D, π, hlim, haff, he⟩ := quotient_fibre_limit_transfer I f B Xs g α p hc hl
    (fun {i j} a ↦ (ht i j a).1) hpg
  have hstage (i : Λᵒᵖ) : CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i) := by
    obtain ⟨e, _⟩ := he i
    let _ : IsProper (g.app i) := hg i
    let q := pullback.snd (g.app i) (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I.comap (α.app i.unop).hom))))
    exact ⟨QuasiCompact.compactSpace_of_compactSpace (e.hom ≫ q),
      quasiSeparatedSpace_of_quasiSeparated (e.hom ≫ q)⟩
  refine ⟨Λ, hpre, hne, hdir, D, π, hlim, haff,
    (fun i ↦ (hstage i).1), (fun i ↦ (hstage i).2), ?_⟩
  intro i
  obtain ⟨e, he₁, he₂⟩ := he i
  exact ⟨B.obj i.unop, inferInstance, hB i.unop, (α.app i.unop).hom,
    Xs.obj i, g.app i, hg i, p.app i, e, hpg i, he₁, he₂⟩

end AlgebraicGeometry.Scheme
