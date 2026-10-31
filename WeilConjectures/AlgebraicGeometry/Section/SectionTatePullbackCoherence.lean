/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons.SectionLocalComparisonData
import WeilConjectures.AlgebraicGeometry.Tate.TatePullbackCompositionLaw

/-! # Tate pullback around compatible sections of a retraction
Source: sk-thm-dnc, local construction, canonical Tate and inverse-image comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open SectionLocalDualizingComparisons

/-- The shifted root-normalized Tate comparison commutes with a compatible pair of
maps and with restriction along a section of a retraction. No exceptional functor,
trace, adjunction, or orientation occurs in this coefficient identity.
Source: sk-thm-dnc, Local construction, standard model, Tate coefficient comparisons
(blueprint: lem-trf-section-tate-pullback-coherence).

Proof: first lift the composition and identity laws of finiteEtaleTwistPullbackData.c
through the degree-zero single functor. The single/pullback comparison is natural;
its composition law follows by the universal property of left derived functors,
or by computing the exact inverse-image functors on complexes. Commute both sides
past the shift 2d, using compatibility of the derived inverse-image compositor with
its canonical shift isomorphism. This proves composition and identity for tatePullback.
Apply composition to the two equal arrows r' followed by v and b followed by r.
Equality transport identifies the common composite, so cancellation gives the
compatible-map square. Apply the same law to b followed by a, and use ba=id.
The identity comparison is leftDerivedUpperStarId, so this last equation is exactly
pullback of tatePullback(a) followed by tatePullback(b), with the section compositor.
Cancel the former comparison to obtain the displayed right side. Empty schemes,
zero coefficients and d=0 use the same unit and compositor equations.
-/
theorem sectionTatePullback_coherence
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' X X' : Scheme.{u}} (a : B ⟶ B') (b : B' ⟶ B) (hba : b ≫ a = 𝟙 B')
    (r : B ⟶ X) (r' : B' ⟶ X') (v : X' ⟶ X) (hr : r' ≫ v = b ≫ r)
    (hB : IsUnit (N : Γ(B, ⊤))) (hB' : IsUnit (N : Γ(B', ⊤)))
    (hX : IsUnit (N : Γ(X, ⊤))) (hX' : IsUnit (N : Γ(X', ⊤))) (d : ℕ) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b r).inv.app
        (SectionLocalDualizingComparisons.tateObject A N hA X d) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r' v (b ≫ r) hr.symm).hom.app
        (SectionLocalDualizingComparisons.tateObject A N hA X d) ≫
      (upperStar (ModuleCat.{u + 1} A) r').leftDerivedFunctor.map
        (tatePullback A N hN hA v hX hX' d).hom ≫
      (tatePullback A N hN hA r' hX' hB' d).hom =
    (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
        (tatePullback A N hN hA r hX hB d).hom ≫
      (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
        (tatePullback A N hN hA a hB' hB d).inv ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) b a hba).hom.app
        (SectionLocalDualizingComparisons.tateObject A N hA B' d)  := by
  have hcomp₁ := tatePullback_composition_identity A N hN hA hB' hX' hX
    r' v (b ≫ r) hr.symm d
  have hcomp₂ := tatePullback_composition_identity A N hN hA hB' hB hX
    b r (b ≫ r) rfl d
  have hcomp₃ := tatePullback_composition_identity A N hN hA hB' hB hB'
    b a (𝟙 B') hba.symm d
  have h₁ :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r' v (b ≫ r) hr.symm).hom.app
          (SectionLocalDualizingComparisons.tateObject A N hA X d) ≫
        (upperStar (ModuleCat.{u + 1} A) r').leftDerivedFunctor.map
          (tatePullback A N hN hA v hX hX' d).hom ≫
        (tatePullback A N hN hA r' hX' hB' d).hom =
      (tatePullback A N hN hA (b ≫ r) hX hB' d).hom := by
    exact hcomp₁.1
  have h₂ :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b r (b ≫ r) rfl).hom.app
          (SectionLocalDualizingComparisons.tateObject A N hA X d) ≫
        (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
          (tatePullback A N hN hA r hX hB d).hom ≫
        (tatePullback A N hN hA b hB hB' d).hom =
      (tatePullback A N hN hA (b ≫ r) hX hB' d).hom := hcomp₂.1
  have h₂' :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b r (b ≫ r) rfl).inv.app
          (SectionLocalDualizingComparisons.tateObject A N hA X d) ≫
        (tatePullback A N hN hA (b ≫ r) hX hB' d).hom =
      (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
          (tatePullback A N hN hA r hX hB d).hom ≫
        (tatePullback A N hN hA b hB hB' d).hom := by
    rw [← h₂]
    simp only [Iso.inv_hom_id_app_assoc]
  have h₃ :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b a (𝟙 B') hba.symm).hom.app
          (SectionLocalDualizingComparisons.tateObject A N hA B' d) ≫
        (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
          (tatePullback A N hN hA a hB' hB d).hom ≫
        (tatePullback A N hN hA b hB hB' d).hom =
      (tatePullback A N hN hA (𝟙 B') hB' hB' d).hom := hcomp₃.1
  have h₃' :
      (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
          (tatePullback A N hN hA a hB' hB d).hom ≫
        (tatePullback A N hN hA b hB hB' d).hom =
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) b a hba).hom.app
        (SectionLocalDualizingComparisons.tateObject A N hA B' d) := by
    apply (cancel_epi
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b a (𝟙 B') hba.symm).hom.app
        (SectionLocalDualizingComparisons.tateObject A N hA B' d))).mp
    unfold leftDerivedUpperStarCompSectionIso
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    calc
      _ = (tatePullback A N hN hA (𝟙 B') hB' hB' d).hom := by
        simpa only [Category.assoc] using h₃
      _ = (leftDerivedUpperStarId (ModuleCat.{u + 1} A) B').hom.app
          (SectionLocalDualizingComparisons.tateObject A N hA B' d) := hcomp₃.2
      _ = _ := by
        rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  let F := (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor
  let e := tatePullback A N hN hA a hB' hB d
  have hb :
      (tatePullback A N hN hA b hB hB' d).hom =
        F.map e.inv ≫
          (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) b a hba).hom.app
            (SectionLocalDualizingComparisons.tateObject A N hA B' d) := by
    apply (cancel_epi (F.map e.hom)).mp
    rw [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]
    exact h₃'
  calc
    _ = (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b r).inv.app
          (SectionLocalDualizingComparisons.tateObject A N hA X d) ≫
        (tatePullback A N hN hA (b ≫ r) hX hB' d).hom := by
          rw [h₁]
    _ = (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
          (tatePullback A N hN hA r hX hB d).hom ≫
        (tatePullback A N hN hA b hB hB' d).hom := h₂'
    _ = _ := by rw [hb]

end AlgebraicGeometry.Etale
