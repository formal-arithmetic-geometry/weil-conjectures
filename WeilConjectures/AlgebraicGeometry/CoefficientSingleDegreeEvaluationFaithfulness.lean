/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BrownTowerRealization
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Evaluation detects maps between systems concentrated in one degree

Source: blueprint sk-prop-sp-integral-adjunction, naturality of the tower Hom chain;
Stacks 06XS and 08J5, full faithfulness of the shifted heart.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules

namespace SheafOfModules

/-- Actual derived evaluation maps jointly detect equality when both evaluated
systems are concentrated in the same degree. No claim of faithfulness on arbitrary
unbounded derived systems is made.
Source: Stacks 06XS and 08J5; blueprint sk-prop-sp-integral-adjunction, natural Hom
bijections (blueprint: lem-pur-single-degree-evaluation-hom-ext).

Proof: use evaluationFactors to identify each evaluation with the localization
of exact ordinary component evaluation. Its normalized homology comparison shows
that every component of H^q(C) and H^q(C') vanishes for q distinct from r. Ordinary
component evaluations jointly detect zero objects, so both whole systems are
concentrated in degree r. Good truncation identifies each with H^r placed in degree
r; full faithfulness of the single functor makes H^r injective on their Hom set.
The equality of evaluated morphisms gives equality after each ordinary component
evaluation of H^r, by naturality of the homology comparisons. Ordinary strict
system maps are determined by their components, so H^r(a) = H^r(b). Injectivity
on the common shifted heart gives a = b. For the zero system this is uniqueness
of the map from or to zero; no bound or quotient-flatness exception is needed. -/
theorem singleDegreeEvaluation_hom_ext
    (W : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (t : O)
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology W) (O := O) (ell := t))
    (C C' : DerivedCategory (BrownTowerComparison.ProSystem W O t)) (r : ℤ)
    (hC : ∀ n, ((P.evaluation n).obj C).IsGE r ∧
      ((P.evaluation n).obj C).IsLE r)
    (hC' : ∀ n, ((P.evaluation n).obj C').IsGE r ∧
      ((P.evaluation n).obj C').IsLE r)
    {a b : C ⟶ C'} (h : ∀ n, (P.evaluation n).map a = (P.evaluation n).map b) :
    a = b := by
  classical
  let ev (n : ℕ) := coefficientEvaluation (J := Scheme.ProEt.topology W)
    (O := O) (ell := t) n
  have hlim (n : ℕ) : PreservesFiniteLimits (ev n) :=
    (coefficientEvaluation_exact (J := Scheme.ProEt.topology W) (O := O) (ell := t) n).1
  have hcol (n : ℕ) : PreservesFiniteColimits (ev n) :=
    (coefficientEvaluation_exact (J := Scheme.ProEt.topology W) (O := O) (ell := t) n).2
  let ei (n : ℕ) : P.evaluation n ≅ (ev n).mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (BrownTowerComparison.ProSystem W O t) (.up ℤ))
      (DerivedCategory.Q ⋙ P.evaluation n)
      (DerivedCategory.Q ⋙ (ev n).mapDerivedCategory)
      (P.evaluation n) (ev n).mapDerivedCategory
      (P.evaluationFactors n ≪≫ (ev n).mapDerivedCategoryFactors.symm)
  let hi (n : ℕ) (q : ℤ) :
      P.evaluation n ⋙ DerivedCategory.homologyFunctor _ q ≅
        DerivedCategory.homologyFunctor _ q ⋙ ev n :=
    Functor.isoWhiskerRight (ei n) (DerivedCategory.homologyFunctor _ q) ≪≫
      ((ev n).mapDerivedCategoryHomologyFunctorIso q).symm
  have hext {M N : BrownTowerComparison.ProSystem W O t} (f g : M ⟶ N)
      (hf : ∀ n, (ev n).map f = (ev n).map g) : f = g := by
    change CoefficientSystem.Hom (J := Scheme.ProEt.topology W) M N at f g
    have hf' : f.app = g.app := funext hf
    cases f
    cases g
    cases hf'
    rfl
  have hz (K : DerivedCategory (BrownTowerComparison.ProSystem W O t))
      (hK : ∀ n, ((P.evaluation n).obj K).IsGE r ∧
        ((P.evaluation n).obj K).IsLE r)
      (q : ℤ) (hq : q ≠ r) : IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply hext
    intro n
    have hk : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((P.evaluation n).obj K)) := by
      rcases lt_or_gt_of_ne hq with hqr | hrq
      · exact (DerivedCategory.isGE_iff _ _).1 (hK n).1 q hqr
      · exact (DerivedCategory.isLE_iff _ _).1 (hK n).2 q hrq
    have hn := hk.of_iso ((hi n q).app K).symm
    exact hn.eq_of_src _ _
  have hge (K : DerivedCategory (BrownTowerComparison.ProSystem W O t))
      (hK : ∀ n, ((P.evaluation n).obj K).IsGE r ∧
        ((P.evaluation n).obj K).IsLE r) : K.IsGE r :=
    (DerivedCategory.isGE_iff K r).2 (fun q hq ↦ hz K hK q (ne_of_lt hq))
  have hle (K : DerivedCategory (BrownTowerComparison.ProSystem W O t))
      (hK : ∀ n, ((P.evaluation n).obj K).IsGE r ∧
        ((P.evaluation n).obj K).IsLE r) : K.IsLE r :=
    (DerivedCategory.isLE_iff K r).2 (fun q hq ↦ hz K hK q (ne_of_gt hq))
  let := hge C hC
  let := hle C hC
  let := hge C' hC'
  let := hle C' hC'
  have hh : (DerivedCategory.homologyFunctor _ r).map a =
      (DerivedCategory.homologyFunctor _ r).map b := by
    apply hext
    intro n
    apply (cancel_epi ((hi n r).hom.app C)).1
    have ha := (hi n r).hom.naturality a
    have hb := (hi n r).hom.naturality b
    dsimp only [Functor.comp_map] at ha hb
    rw [← ha, ← hb, h n]
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE C r
  obtain ⟨N, ⟨e'⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE C' r
  apply (cancel_epi e.inv).1
  apply (cancel_mono e'.hom).1
  obtain ⟨f, hf⟩ := (DerivedCategory.singleFunctor _ r).map_surjective
    (e.inv ≫ a ≫ e'.hom)
  obtain ⟨g, hg⟩ := (DerivedCategory.singleFunctor _ r).map_surjective
    (e.inv ≫ b ≫ e'.hom)
  simp only [Category.assoc]
  rw [← hf, ← hg]
  congr 1
  have : (DerivedCategory.singleFunctor (BrownTowerComparison.ProSystem W O t) r ⋙
      DerivedCategory.homologyFunctor _ r).Faithful :=
    Functor.Faithful.of_iso (DerivedCategory.singleFunctorCompHomologyFunctorIso _ r).symm
  apply (DerivedCategory.singleFunctor _ r ⋙
    DerivedCategory.homologyFunctor _ r).map_injective
  change (DerivedCategory.homologyFunctor _ r).map
      ((DerivedCategory.singleFunctor _ r).map f) = _
  dsimp only [Functor.comp_map]
  rw [hf, hg]
  simp only [Functor.map_comp, hh]

end SheafOfModules
