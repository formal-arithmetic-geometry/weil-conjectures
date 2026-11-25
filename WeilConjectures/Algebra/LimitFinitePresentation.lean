/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.Algebra.LimitFinitePresentation.Core
import WeilConjectures.Algebra.LimitFinitePresentation.Colimits

/-! # Noetherian approximation of a finitely presented ring map

## References

* [Stacks Project, Tag 00R0](https://stacks.math.columbia.edu/tag/00R0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Algebra

/-- Noetherian approximation of a finitely presented ring map: it is a filtered colimit of
finite-type maps between finite-type `ℤ`-algebras, with the stated pushout squares. -/
theorem exists_limit_finite_presentation
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.FinitePresentation φ) :
    ∃ (Λ : Type u) (_hpo : Preorder Λ) (_hne : Nonempty Λ)
      (_hdir : IsDirected Λ (fun a b => a ≤ b))
      (Rfun : Λ ⥤ CommRingCat) (Sfun : Λ ⥤ CommRingCat)
      (η : Rfun ⟶ Sfun) (cR : Cocone Rfun) (cS : Cocone Sfun),
      cR.pt = CommRingCat.of R ∧ cS.pt = CommRingCat.of S ∧
      (∀ l (hR : cR.pt = CommRingCat.of R) (hS : cS.pt = CommRingCat.of S),
        η.app l ≫ cS.ι.app l = cR.ι.app l ≫
          (eqToHom hR ≫ CommRingCat.ofHom φ ≫ eqToHom hS.symm)) ∧
      (∀ l, RingHom.FiniteType (η.app l).hom) ∧
      (∀ l, RingHom.FiniteType (algebraMap ℤ (Rfun.obj l))) ∧
      (∀ l m (h : l ≤ m),
        Nonempty (CategoryTheory.IsPushout (η.app l) (Rfun.map (homOfLE h))
          (Sfun.map (homOfLE h)) (η.app m))) ∧
      (∀ l (hR : cR.pt = CommRingCat.of R) (hS : cS.pt = CommRingCat.of S),
        Nonempty (CategoryTheory.IsPushout (η.app l) (cR.ι.app l) (cS.ι.app l)
          (eqToHom hR ≫ CommRingCat.ofHom φ ≫ eqToHom hS.symm))) ∧
      Nonempty (IsColimit cR) ∧ Nonempty (IsColimit cS)
:= by
  obtain ⟨Λ, hpo, hne, hdir, Rfun, Sfun, η, cR, cS, hcore⟩ :=
    exists_limit_finite_presentation_core φ hφ
  rcases hcore with ⟨hR, hS, hcompat, hft, hRft, hpush, hfinal, hcolR⟩
  let : Nonempty Λ := hne
  let : IsDirected Λ (fun a b => a ≤ b) := hdir
  have hcolS := colimits_of_limit_finite_presentation_core η cR cS
    (eqToHom hR ≫ CommRingCat.ofHom φ ≫ eqToHom hS.symm)
    (fun l => hfinal l hR hS) hcolR.some
  exact ⟨Λ, hpo, hne, hdir, Rfun, Sfun, η, cR, cS, hR, hS, hcompat, hft,
    hRft, hpush, hfinal, hcolR, hcolS⟩

end Algebra
