/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.RingTheory.SmoothPushoutFilteredColimitStage

/-!
# Smoothness of an affine model over an affine inverse system

Source: Stacks Project, Tags 0C0C, 0CAQ and 01ZM(2)-(3).
(blueprint: lem-sbc-affine-diagram-smooth-stage)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Smoothness of a fixed finitely presented affine model descends along an affine system.

Source: Stacks Project, Tag 0C0C, affine case, using Tags 0CAQ and 01ZM(2)-(3).
Proof: an inverse limit of affine schemes is affine. Its global sections are the
filtered colimit of the stage rings. Write A for the ring of Q and B for the ring
of P; B is finitely presented over A. The compatible maps to Q give compatible
A-algebra structures on the stage rings and their colimit. Smoothness of the
limit pullback says that the base change of B to this colimit is smooth. Tag 0CAQ
provides a smooth finitely presented model over one stage. Compare its base change
with that of B. Descend the comparison isomorphism and its inverse to a common
later stage by Tag 01ZM(2), and descend their composite identities by 01ZM(3).
The base change of B at that stage is isomorphic to a smooth algebra and hence
smooth. Translate back by the affine criterion for smooth scheme morphisms.
The index category is nonempty by cofilteredness; zero rings and empty spectra
are allowed throughout, and no nonempty-source hypothesis is used.
(blueprint: lem-sbc-affine-diagram-smooth-stage) -/
theorem exists_smooth_stage_of_affine_diagram {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ j, IsAffine (D.obj j))
    {Q P : Scheme.{u}} [IsAffine Q] [IsAffine P]
    (t : D ⟶ (Functor.const I).obj Q) (s : c.pt ⟶ Q)
    (hs : ∀ j, c.π.app j ≫ t.app j = s)
    (p : P ⟶ Q) [LocallyOfFinitePresentation p]
    [Smooth (pullback.snd p s)] :
    ∃ j, Smooth (pullback.snd p (t.app j)) := by
  have (j : I) : IsAffine (D.obj j) := hD j
  have : ∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f) := fun f ↦ inferInstance
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let F := D.op ⋙ Scheme.Γ
  let d := Scheme.Γ.mapCocone c.op
  let tR : (Functor.const Iᵒᵖ).obj Γ(Q, ⊤) ⟶ F :=
    { app := fun j ↦ (t.app j.unop).appTop
      naturality := fun j k f ↦ by
        dsimp [F]
        rw [Category.id_comp, ← Scheme.Hom.comp_appTop]
        congr 1
        simp only [Functor.const_obj_obj] at *
        exact (t.naturality f.unop).symm }
  have hsR (j : Iᵒᵖ) : tR.app j ≫ d.ι.app j = s.appTop := by
    change (t.app j.unop).appTop ≫ (c.π.app j.unop).appTop = _
    rw [← Scheme.Hom.comp_appTop, hs]
  have hp := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)
    (f := p)).mp ‹_›
  have hsm := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)
    (f := pullback.snd p s)).mp ‹_›
  obtain ⟨j, hj⟩ := CommRingCat.exists_smooth_pushout_stage F d
    (nonempty_isColimit_Γ_mapCocone D c hc).some p.appTop hp tR s.appTop hsR
    (fun j ↦ Γ(pullback p (t.app j.unop), ⊤))
    (fun j ↦ (pullback.fst p (t.app j.unop)).appTop)
    (fun j ↦ (pullback.snd p (t.app j.unop)).appTop)
    (fun j ↦ isPushout_appTop_of_isPullback (IsPullback.of_hasPullback p (t.app j.unop)))
    (pullback.fst p s).appTop (pullback.snd p s).appTop
    (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback p s)) hsm
  exact ⟨j.unop, (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mpr hj⟩

end AlgebraicGeometry.Scheme
