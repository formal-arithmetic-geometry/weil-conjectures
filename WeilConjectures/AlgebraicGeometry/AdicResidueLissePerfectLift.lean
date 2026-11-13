/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.AdicCompleteHomSections
import WeilConjectures.AlgebraicGeometry.AdicCompleteResidueConservative
import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionHomML
import WeilConjectures.AlgebraicGeometry.AdicResidueFiniteLocalModels
import Mathlib.CategoryTheory.Limits.Types.Images

/-!
# Local perfect lifting from lisse residue complexes

Source: Stacks Project, Tag 09C6; Bhatt--Scholze, Lemma 6.6.8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Choose a compatible family whose first term has a property attained from every level.
This is the stable-image step of Stacks Tag 09C6. -/
private theorem adicResidue_sections_with_property
    (F : ℕᵒᵖ ⥤ Type w) (hF : F.IsMittagLeffler)
    (p : F.obj (op 0) → Prop)
    (hp : ∀ n : ℕ, ∃ x : F.obj (op n),
      p (F.map (homOfLE (Nat.zero_le n)).op x)) :
    ∃ x : F.sections, p (x.val (op 0)) := by
  classical
  obtain ⟨n, f, hf⟩ := F.isMittagLeffler_iff_eventualRange.mp hF (op 0)
  obtain ⟨x, hx⟩ := hp n.unop
  have hfx : p (F.map f x) := by
    have he : f = (homOfLE (Nat.zero_le n.unop)).op := Subsingleton.elim _ _
    simpa only [he] using hx
  let y : (F.toEventualRanges).obj (op 0) := ⟨F.map f x, hf.symm ▸ ⟨x, rfl⟩⟩
  obtain ⟨z, hz⟩ := Types.surjective_π_app_zero_of_surjective_map
    (Types.limitConeIsLimit F.toEventualRanges)
    (fun n ↦ F.surjective_toEventualRanges hF (homOfLE (Nat.le_succ n)).op) y
  refine ⟨F.toEventualRangesSectionsEquiv z, ?_⟩
  exact (congrArg (fun t : (F.toEventualRanges).obj (op 0) ↦ p t.val) hz).mpr hfx

/-- Conjugated scalar extension carries an invertible finite-level map to an invertible map. -/
private theorem adicResidueHomTower_isIso_zero
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ)
    (f : (adicResidueLocalReduction.{u, v} X J U n).obj T ⟶
      (adicResidueLocalReduction.{u, v} X J U n).obj M) (hf : IsIso f) :
    IsIso ((adicResidueHomTower.{u, v} X J U T M).map (homOfLE (Nat.zero_le n)).op f) := by
  induction n with
  | zero =>
    simpa only [show (homOfLE (Nat.zero_le 0)).op = 𝟙 (op 0) from rfl,
      Functor.map_id_apply] using hf
  | succ n ih =>
    have he : (homOfLE (Nat.zero_le (n + 1))).op =
        (homOfLE (Nat.le_succ n)).op ≫ (homOfLE (Nat.zero_le n)).op := Subsingleton.elim _ _
    rw [he, Functor.map_comp_apply]
    dsimp only [adicResidueHomTower]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    change IsIso ((adicResidueHomTower.{u, v} X J U T M).map (homOfLE (Nat.zero_le n)).op
      (adicResidueHomStep.{u, v} X J U T M n f))
    apply ih
    have := hf
    dsimp only [adicResidueHomStep]
    infer_instance

/-- A complete completed-coefficient complex with bounded lisse finite-Tor residue has
bounded finite-projective constant local models (Stacks, Tags 09C6 and 099L;
Bhatt--Scholze, Lemma 6.6.8 and Proposition 6.6.11). -/
theorem adicResidueLissePerfectLift
    (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A]
    (M : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J))
    (_hcomplete : CategoryTheory.ConstantCompletion.IsComplete
      (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X) A
        J 0) M)
    (C : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A J 0))
    (_hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (_hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) (A ⧸ J ^ (0 + 1))
      ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (a b : ℤ) (_hab : a ≤ b)
    (_htor : ∀ P : CategoryTheory.ConstantCompletion.Cx
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := smallModelComparisonEtaleTopology.{u, v} X)
        (R := CategoryTheory.ConstantCompletion.finite
          (smallModelComparisonEtaleTopology.{u, v} X) A J 0) P →
      Nonempty ((CategoryTheory.ConstantCompletion.Q
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)).obj P ≅ C) →
      ∀ (N : CategoryTheory.ConstantCompletion.Mod
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0))
        (q : ℤ), q < a ∨ b < q →
        IsZero (adicResidueTensorCohomology.{max v (u + 1)}
          (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X)
            A J 0) P N q))
    (_hres : Nonempty
      ((CategoryTheory.ConstantCompletion.extend
        (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X)
          A J 0)).obj M ≅
        (adicResidueComparison.{u, v} X (A ⧸ J ^ (0 + 1))).obj C)) :
    ∃ S : Sieve ((AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj (⊤_ X.ProEt)),
      S ∈ coefficientProEtaleModelTopology.{u, v} X _ ∧
      ∀ (U : coefficientProEtaleSiteModel.{u, v} X)
        (f : U ⟶ (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj (⊤_
          X.ProEt)), S f →
        ∃ (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (c d : ℤ),
          P.IsStrictlyGE c ∧ P.IsStrictlyLE d ∧
          (∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) ∧
          Nonempty
            ((adicResidueRestriction.{max v (u + 1)}
              (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u,
                v} X) A J) U).obj M ≅
              (adicResidueRestriction.{max v (u + 1)}
                (CategoryTheory.ConstantCompletion.completed
                  (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
                    (adicResidueConstantPerfect.{u, v} X J P)) := by
  classical
  obtain ⟨S, hS, hmodels⟩ := adicResidue_finite_local_models.{u, v} X J M _hcomplete C
    _hbounded _hlisse a b _hab _htor _hres
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨V, R, P, c, d, hc, hd, hP, hAffine, hV, eM, eT, hT, hM, hfinite⟩ :=
    hmodels U f hf
  obtain ⟨eM⟩ := eM
  obtain ⟨eT⟩ := eT
  let B := CategoryTheory.ConstantCompletion.completed
    (coefficientProEtaleModelTopology.{u, v} X) A J
  let T := (adicResidueRestriction B V).obj (adicResidueConstantPerfect X J P)
  let L := (adicResidueRestriction B V).obj M
  let G := adicResidueHomTower.{u, v} X J V T L
  have hML : G.IsMittagLeffler :=
    adicResidueHomTower_mittagLeffler.{u, v} X J V hAffine hV P c d hc hd hP L hM hfinite
  obtain ⟨s, hs⟩ := adicResidue_sections_with_property G hML (fun g ↦ IsIso g) (by
    intro n
    obtain ⟨e⟩ := hfinite n
    exact ⟨e.hom, adicResidueHomTower_isIso_zero.{u, v} X J V T L n e.hom inferInstance⟩)
  obtain ⟨g, hg⟩ := adicResidueHomSection_surjective.{u, v} X J V T L hM s
  have hresidue : IsIso ((adicResidueLocalReduction.{u, v} X J V 0).map g) := by
    have h := congrArg (fun t : G.sections ↦ t.val (op 0)) hg
    change (adicResidueLocalReduction.{u, v} X J V 0).map g = s.val (op 0) at h
    exact h.symm ▸ hs
  have := adicResidue_isIso_of_residue.{u, v} X J V T L hT hM g hresidue
  exact ⟨P, c, d, hc, hd, hP, ⟨eM.symm ≪≫ R.mapIso (asIso g).symm ≪≫ eT⟩⟩

end AlgebraicGeometry.Scheme
