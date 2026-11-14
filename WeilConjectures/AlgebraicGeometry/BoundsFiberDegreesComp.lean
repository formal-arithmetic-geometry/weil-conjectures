/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteFieldTowerDegreeBound

/-!
# Fibre degree bounds under composition

## Main statements

* `AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_comp`: fibre degree bounds multiply.
* `AlgebraicGeometry.Scheme.Hom.hasUniversallyBoundedFibers_comp`: uniform bounds compose.

## References

* Stacks Project, Tag 03J6
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

private theorem finite_of_finite_fibers_over_field {X Y : Scheme.{u}}
    {K : Type u} [Field K] (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) [IsFinite g]
    (hf : ∀ y, IsFinite (f.fiberToSpecResidueField y)) : IsFinite f := by
  have : LocallyQuasiFinite f := .of_fiberToSpecResidueField f fun y ↦ by
    let := hf y
    infer_instance
  have : IsLocallyArtinian Y := .of_locallyQuasiFinite g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : IsArtinianScheme Y := ⟨⟩
  have hX : (Set.univ : Set X).Finite := by
    apply Set.Finite.of_finite_fibers f (Set.toFinite _)
    intro y _
    let := hf y
    have : IsLocallyArtinian (f.fiber y) :=
      .of_locallyQuasiFinite (f.fiberToSpecResidueField y)
    have : CompactSpace (f.fiber y) :=
      QuasiCompact.compactSpace_of_compactSpace (f.fiberToSpecResidueField y)
    have : IsArtinianScheme (f.fiber y) := ⟨⟩
    have : Finite (f ⁻¹' {y}) := Finite.of_equiv _ (f.fiberHomeo y).toEquiv
    simpa only [Set.univ_inter] using (Set.toFinite (f ⁻¹' {y}))
  have : Finite X := Set.finite_univ_iff.mp hX
  exact IsFinite.of_locallyQuasiFinite f

/-- Fibre degree bounds multiply under composition (Stacks Project, Morphisms, Tag 03J6). -/
theorem boundsFiberDegrees_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n m : ℕ) (hf : BoundsFiberDegrees f n) (hg : BoundsFiberDegrees g m) :
    BoundsFiberDegrees (f ≫ g) (n * m) := by
  intro z
  let fz := Limits.pullback.snd f (g.fiberι z)
  let gz := g.fiberToSpecResidueField z
  have hgz : IsFinite gz := (hg z).1
  let := hgz
  have hfz : BoundsFiberDegrees fz n :=
    boundsFiberDegrees_pullback_snd f (g.fiberι z) n hf
  have hfzfin : IsFinite fz :=
    finite_of_finite_fibers_over_field fz gz fun y ↦ (hfz y).1
  let := hfzfin
  have H := (IsPullback.of_hasPullback f (g.fiberι z)).paste_vert
    (IsPullback.of_hasPullback g (Z.fromSpecResidueField z))
  have he : H.isoPullback.inv ≫ (fz ≫ gz) =
      (f ≫ g).fiberToSpecResidueField z := H.isoPullback_inv_snd
  have hfinite : IsFinite ((f ≫ g).fiberToSpecResidueField z) := by
    rw [← he]
    infer_instance
  refine ⟨hfinite, ?_⟩
  have hdeg := finrankΓ_comp_le_mul_of_finite fz gz n fun y ↦ (hfz y).2
  have hrank : (fz ≫ gz).finrankΓ =
      ((f ≫ g).fiberToSpecResidueField z).finrankΓ :=
    finrankΓ_eq_of_iso _ _ H.isoPullback (Iso.refl _) (by
      rw [Iso.refl_hom, Spec.map_id, Category.comp_id]
      change H.isoPullback.hom ≫ Limits.pullback.snd (f ≫ g) (Z.fromSpecResidueField z) =
        Limits.pullback.snd f (g.fiberι z) ≫ Limits.pullback.snd g (Z.fromSpecResidueField z)
      exact H.isoPullback_hom_snd)
  rw [← hrank]
  exact hdeg.trans (Nat.mul_le_mul_left n (hg z).2)

/-- A composition of morphisms with universally bounded fibres has universally bounded
fibres (Stacks Project, Morphisms, Tag 03J6). -/
theorem hasUniversallyBoundedFibers_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasUniversallyBoundedFibers f) (hg : HasUniversallyBoundedFibers g) :
    HasUniversallyBoundedFibers (f ≫ g) := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨m, hm⟩ := hg
  exact ⟨n * m, boundsFiberDegrees_comp f g n m hn hm⟩

end AlgebraicGeometry.Scheme.Hom
