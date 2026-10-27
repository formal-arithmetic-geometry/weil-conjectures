/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE, SHEAF group C8
-/
module

public import Sheaf.DeligneLaumon.RawHeartAdicLisseData
import Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge
import Sheaf.DeligneLaumon.RawHeartAdicStrataBridge
import Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge
import Sheaf.Paper.ZlSfPbcNormalizedHeartModel

/-! # Assembly of classical lisse strata in the raw adic heart

Source: blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7;
Bhatt--Scholze, Section 6.8
(blueprint: lem-zl-raw-heart-adic-lisse-stratification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.RawHeartAdic
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Classical lisse strata at one finite coefficient field, with normalized comparisons,
Weil lifts on descended pieces, and one finite-field smooth affine frontier refinement.

Source: blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7;
BS 6.8.4, 6.8.13, 6.8.14(2), 6.8.15
(blueprint: lem-zl-raw-heart-adic-lisse-stratification).

Proof: Obtain the normalized lisse family, completed-system comparison, coherent
identity-induced coefficient system and continuous realization from their recorded
existence theorems. The comparison bridge supplies their normalized classical family.
Apply the normalized heart-model theorem to obtain one finite heart representative
and its constructible continuous sheaf. Apply the finite-strata bridge at that same
stage; insert its reduced partition, bases and classical models into Strata, together
with the supplied representative isomorphism. Apply the restriction bridge to these
chosen strata to obtain the frontier and actual rational Weil-lift clauses. Assemble
the witnesses and conjunctions. No new coefficient stage is chosen for the strata.
-/
theorem raw_heart_adic_lisse_stratification (iota : Ω ≃+* ℂ)
    (X : PerAdic.Base D.k) (M : sfCommonStageHeart l X.scheme Ω) :
    ∃ (a : LisseRealization.Family D l hl) (c : ProEtale.CompletedLisse.System.{u} l)
      (b : ClassicalFamily D l hl a c) (S : FdCoefficientComparisonSystem.{u} l Ω)
      (r : ContinuousRational.Family.{u} l),
      Normalized D l hl Ω a ∧ FdComparisonSchemeCoherence l Ω S ∧
      (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
        (Y : PerAdic.Base D.k), Nonempty (CondensedCoefficients D l A Y)) ∧
      (∀ Y : PerAdic.Base D.k,
        Nonempty (HeartComparison D l hl Ω a S r Y
          (hDim := baseDimension D l hl Y) (hInv := basePrimeUnit D l hl Y))) ∧
      (∀ Y : PerAdic.Base D.k, Nonempty (ClassicalCommon D l hl Ω a c b Y)) ∧
      ∃ s : Strata D l hl Ω a c b X M,
        (∀ (Y₀ : Over (Spec (.of D.k₀)))
          [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
          (e : X.scheme ≅ (D.geometricFiber Y₀).left.nilradical.subscheme),
          Nonempty (Frontier D l hl Ω s Y₀ e)) ∧
        (∀ (Y₀ : Over (Spec (.of D.k₀)))
          [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
          (e : X.scheme ≅ (D.geometricFiber Y₀).left)
          (K : sfCommonStageWeilComplex D l hl Y₀ Ω),
          Nonempty ((pullCommon D l hl Ω (X := X) (Y := geometricBase D Y₀) e.hom).obj
            K.carrier ≅ M.obj) →
          ∀ (ν : Fin s.partition.n) (m : ℕ) (hm : 1 ≤ m)
            (V₀ : Over (Spec (.of (D.extensionSubfield m hm))))
            (j₀ : V₀ ⟶ finiteModel D Y₀ m hm), IsImmersion j₀.left →
          ∀ (W : PerAdic.Base D.k)
            (eW : W.scheme ≅ ((geometricChange D m hm).obj V₀).left),
            eW.hom ≫ ((geometricChange D m hm).obj V₀).hom =
              (W.scheme ↘ Spec (.of D.k)) →
          ∀ (j : W.scheme ⟶ (s.bases ν).scheme), IsImmersion j →
            (j ≫ eqToHom (s.domain ν) ≫ s.partition.immersion ν ≫ e.hom) ≫
                pullback.fst Y₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
              eW.hom ≫ pullback.fst V₀.hom
                (Spec.map (CommRingCat.ofHom (algebraMap (D.extensionSubfield m hm) D.k))) ≫
                j₀.left ≫ pullback.fst Y₀.hom
                  (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) →
            (j ≫ eqToHom (s.domain ν) ≫ s.partition.immersion ν ≫ e.hom) ≫
                (D.geometricFiber Y₀).hom = (W.scheme ↘ Spec (.of D.k)) →
            Nonempty (WeilLift D l hl Ω s Y₀ e K ν m hm V₀ W eW j)) := by
  classical
  have _ := iota
  obtain ⟨a, _, hpull, hfield, hpoint, hcommon⟩ :=
    LisseRealization.lisse_rational_realization D l hl
  have ha : Normalized D l hl Ω a := ⟨hpull, hfield, hpoint, hcommon Ω⟩
  obtain ⟨c⟩ := ProEtale.CompletedLisse.completed_system_comparison l
  obtain ⟨S, hS, _⟩ := rationalCoefficientCategoryComparison l Ω D hl
  obtain ⟨r⟩ := ContinuousRational.continuous_rational_derived_realization l
  obtain ⟨b, hcoeff, hheart, hclassical⟩ :=
    raw_heart_adic_comparison_bridge D l hl Ω a ha c S hS r
  obtain ⟨B, I, ⟨H⟩⟩ := zlSfPbcNormalizedHeartModel l Ω D hl S r
  let := B
  let := I
  let Z : ZlHeartBase D :=
    { scheme := X.scheme
      structureMap := X.scheme ↘ Spec (.of D.k) }
  obtain ⟨i, N, hN, ⟨e⟩, F, hF, hreal⟩ := H.heart.finite_heart Z M
  let Nheart : sfRationalHeart l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X.scheme := ⟨N, hN⟩
  obtain ⟨partition, hred, bases, domain, hbase, model, hrestr⟩ :=
    raw_heart_adic_strata_bridge D l hl Ω a c b S r hheart X i Nheart F hF hreal
  let s : Strata D l hl Ω a c b X M :=
    { stage := i
      finite := Nheart
      representative := e
      partition := partition
      reduced := hred
      bases := bases
      domain := domain
      base_map := hbase
      model := model
      restriction := fun ν ↦ Classical.choice (hrestr ν) }
  obtain ⟨hfrontier, hweil⟩ :=
    raw_heart_adic_restriction_bridge D l hl Ω a ha c b hclassical X M s
  exact ⟨a, c, b, S, r, ha, hS, hcoeff, hheart, hclassical, s, hfrontier, hweil⟩

end WeilConjectures.RawHeartAdic
