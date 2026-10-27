/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Paper.ConstructibleExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Etale witnesses and transport by the comparison unit

Source: main-20261015, thm-pur-general-admissibility.proof.md, Step 2;
Stacks Project, Tags 09AK, 09AL, 099V and 09B1
(blueprint: lem-pur-etale-witness-transport-data).

The functors use ordinary constant-coefficient module sheaves. The canonical exact
constant-ring realization is used only to evaluate the recorded intrinsic predicates.
The comparison and the identification of each witness are actual constructions from
its specified adjunction unit. No additivity or exactness of G is required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The ordinary bounded-below etale category, with the site's coefficient-size convention.
Source: blueprint def-sf-categories (blueprint: lem-pur-etale-witness-transport-data). -/
abbrev witnessEtalePlus (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The ordinary bounded-below pro-etale category in the identical coefficient universe.
Source: blueprint def-sf-categories (blueprint: lem-pur-etale-witness-transport-data). -/
abbrev witnessProEtalePlus (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- H = nu_Z^* G Rnu_T,*; composition is written in diagrammatic order.
Source: blueprint Step 2 (blueprint: lem-pur-etale-witness-transport-data). -/
def witnessTransportFunctor (A : Type (u + 1)) [CommRing A] (T Z : Scheme.{u})
    (G : witnessEtalePlus A T ⥤ witnessEtalePlus A Z) :
    witnessProEtalePlus A T ⥤ witnessProEtalePlus A Z :=
  (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctorPlus ⋙
    G ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus

/-- The natural comparison H nu_T^* ≅ nu_Z^* G, constructed from the inverse of
exactly the derived adjunction unit, whiskered by F = nu_Z^* G.
Source: Stacks 099V, 09B1 (blueprint: lem-pur-etale-witness-transport-data). -/
def witnessTransportComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (T Z : Scheme.{u}) (G : witnessEtalePlus A T ⥤ witnessEtalePlus A Z) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        witnessTransportFunctor A T Z G ≅
      G ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compactSupportComparisonUnit T A).symm _ ≪≫
      Functor.leftUnitor _

/-- Delta for a retained origin witness is H(alpha)^{-1} followed by the component
of the comparison. All data are supplied by the witness and the specified unit.
Source: blueprint Step 2 (blueprint: lem-pur-etale-witness-transport-data). -/
def witnessTransportIdentification (A : Type (u + 1)) [CommRing A] [Finite A]
    (T Z : Scheme.{u}) (G : witnessEtalePlus A T ⥤ witnessEtalePlus A Z)
    (B : witnessProEtalePlus A T) (B_e : witnessEtalePlus A T)
    (alpha : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj B_e
      ≅ B) :
    (witnessTransportFunctor A T Z G).obj B ≅
      (G ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus).obj B_e :=
  ((witnessTransportFunctor A T Z G).mapIso alpha).symm ≪≫
    (witnessTransportComparison A T Z G).app B_e

/-- Constructible origins exist without any Tor hypothesis; every witness reflects the
cohomological interval and, separately, the assumed pro-etale Tor interval. The explicit
natural derived comparison and all witness identifications have the specified unit
normalization, uniqueness and naturality, including noninvertible beta and h.
Source: main-20261015 thm-pur-general-admissibility.proof.md, Step 2; Stacks 09AL,
09AK, 099V, 09B1 (blueprint: lem-pur-etale-witness-transport-data).

Proof:
1. Apply lem-sf-proetale-constructible-origin (ii) to the finite quotient A and the
intrinsically bounded constructible B. Its exact realization equivalence identifies
these predicates with the fixed-scalar presentation and supplies B_e and alpha.
2. For any witness, lem-sf-comparison-pullback-exact identifies cohomology degreewise.
Exactness preserves zero sheaves; the unit of thm-weil-pbc-site-comparison applied to
an etale sheaf in degree zero reflects zero sheaves. This proves interval reflection.
3. If B has the Tor interval, apply lem-sf-comparison-tor-amplitude (ii) with
K = B, K' = B_e and alpha inverse, using canonical realization. Ell is invertible
on T since T is over k and ell differs from its characteristic. This tests every
etale module sheaf, and applies to each witness separately.
4. Apply F = nu_Z^* G to the invertible natural unit eta on all of D+.
This gives sigma = F(eta), whose inverse is witnessTransportComparison.
Functoriality and unit naturality prove its naturality without any assumption on G.
5. For each witness set t = H(alpha) sigma and delta = t inverse, as constructed
above. Its inverse is F(eta) followed by F(Rnu_* alpha); uniqueness of inverses
shows this formula characterizes delta.
6. If alpha h = nu_T^*(beta) alpha', then H(h) t = t' F(beta), by functoriality
and unit naturality. Compose with the inverses of t and t' to obtain the displayed
naturality identity. Neither beta nor h is inverted. -/
theorem etaleWitnessTransportData (P : WeilConjectures.PurityFiniteSetting.{u})
    (T Z : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (G : witnessEtalePlus P.Coefficient T ⥤ witnessEtalePlus P.Coefficient Z)
    (r s : ℤ) (_hrs : r ≤ s) :
    (∀ B : witnessProEtalePlus P.Coefficient T,
      Scheme.intrinsicFiniteTorsionConstructible
        P.coefficients.l P.extension P.level P.level_pos T
        ((finiteCoefficientIntrinsicRealization T P.Ring).mapDerivedCategory.obj B.obj) →
      (∃ B_e : witnessEtalePlus P.Coefficient T,
        Etale.DerivedCategory.isBoundedConstructible P.Coefficient T B_e.obj ∧
        Nonempty
          ((comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.obj B_e ≅ B)) ∧
      (∀ (B_e : witnessEtalePlus P.Coefficient T),
        Etale.DerivedCategory.isBoundedConstructible P.Coefficient T B_e.obj →
        ∀ _alpha : (comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.obj B_e ≅ B,
          (_root_.DerivedCategory.homologyConcentratedIn r s B_e.obj ↔
            WeilConjectures.constructibleInterval
              P.coefficients.l P.extension P.level P.level_pos T r s
              ((finiteCoefficientIntrinsicRealization T P.Ring).mapDerivedCategory.obj B.obj)) ∧
          (Scheme.HasProEtaleTorAmplitude T P.Ring
              ((finiteCoefficientIntrinsicRealization T P.Ring).mapDerivedCategory.obj B.obj)
              r s →
            Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T r s B_e.obj))) ∧
    (∀ C : witnessEtalePlus P.Coefficient T,
      (witnessTransportComparison P.Coefficient T Z G).inv.app C =
        (G ⋙ (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategoryPlus).map
          ((derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} P.Coefficient) T).unit.app C)) ∧
    (∀ (B : witnessProEtalePlus P.Coefficient T)
        (_hB : Scheme.intrinsicFiniteTorsionConstructible
          P.coefficients.l P.extension P.level P.level_pos T
          ((finiteCoefficientIntrinsicRealization T P.Ring).mapDerivedCategory.obj B.obj))
        (B_e : witnessEtalePlus P.Coefficient T)
        (_hBe : Etale.DerivedCategory.isBoundedConstructible P.Coefficient T B_e.obj)
        (alpha : (comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.obj B_e ≅ B),
      (witnessTransportIdentification P.Coefficient T Z G B B_e alpha).inv =
        (G ⋙ (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategoryPlus).map
          ((derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} P.Coefficient) T).unit.app B_e) ≫
        (G ⋙ (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategoryPlus).map
          ((comparisonLowerStar
            (ModuleCat.{u + 1} P.Coefficient) T).rightDerivedFunctorPlus.map alpha.hom)) ∧
    (∀ (B B' : witnessProEtalePlus P.Coefficient T)
        (_hB : Scheme.intrinsicFiniteTorsionConstructible
          P.coefficients.l P.extension P.level P.level_pos T
          ((finiteCoefficientIntrinsicRealization T P.Ring).mapDerivedCategory.obj B.obj))
        (_hB' : Scheme.intrinsicFiniteTorsionConstructible
          P.coefficients.l P.extension P.level P.level_pos T
          ((finiteCoefficientIntrinsicRealization T P.Ring).mapDerivedCategory.obj B'.obj))
        (B_e B'_e : witnessEtalePlus P.Coefficient T)
        (_hBe : Etale.DerivedCategory.isBoundedConstructible P.Coefficient T B_e.obj)
        (_hBe' : Etale.DerivedCategory.isBoundedConstructible P.Coefficient T B'_e.obj)
        (alpha : (comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.obj B_e ≅ B)
        (alpha' : (comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.obj B'_e ≅ B')
        (beta : B_e ⟶ B'_e) (h : B ⟶ B'),
      alpha.hom ≫ h =
          (comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.map beta ≫ alpha'.hom →
      (witnessTransportFunctor P.Coefficient T Z G).map h ≫
          (witnessTransportIdentification P.Coefficient T Z G B' B'_e alpha').hom =
        (witnessTransportIdentification P.Coefficient T Z G B B_e alpha).hom ≫
          (G ⋙ (comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategoryPlus).map beta) := by
  classical
  let N := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T
  let E := finiteCoefficientIntrinsicRealization T P.Ring
  have : E.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact T P.Ring).1
  have : E.Additive := finiteCoefficientIntrinsicRealization_additive T P.Ring
  have : PreservesFiniteLimits E :=
    finiteCoefficientIntrinsicRealization_preservesFiniteLimits T P.Ring
  have : PreservesFiniteColimits E :=
    finiteCoefficientIntrinsicRealization_preservesFiniteColimits T P.Ring
  have hcomparison (C : witnessEtalePlus P.Coefficient T) :
      (witnessTransportComparison P.Coefficient T Z G).inv.app C =
        (G ⋙ (comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategoryPlus).map
            ((derivedComparisonAdjunctionPlus
              (ModuleCat.{u + 1} P.Coefficient) T).unit.app C) := by
    simp [witnessTransportComparison, compactSupportComparisonUnit]
  refine ⟨?_, hcomparison, ?_, ?_⟩
  · intro B hB
    have hfinite := Scheme.finiteRing_constructibleDerived_origin T P.Ring
    let K := E.mapDerivedCategory.obj B.obj
    have hbounds : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
      obtain ⟨a, ha⟩ := hB.1.bddBelow
      obtain ⟨b, hb⟩ := hB.1.bddAbove
      refine ⟨min a b, b, min_le_right _ _, ?_⟩
      intro i hi
      by_contra hz
      rcases hi with hi | hi
      · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (not_lt_of_ge (hb hz)) hi
    constructor
    · obtain ⟨L, ⟨eL⟩⟩ := (hfinite.2.2.1 K).mpr ⟨hB.2, hbounds⟩
      have hLplus : DerivedCategory.TStructure.t.plus L.obj := by
        obtain ⟨a, b, _, hv⟩ := L.property.2
        exact ⟨a, (DerivedCategory.isGE_iff L.obj a).mpr
          (fun i hi ↦ hv i (Or.inl hi))⟩
      let Lplus : witnessEtalePlus P.Coefficient T := ⟨L.obj, hLplus⟩
      let e : N.mapDerivedCategory.obj L.obj ≅ B.obj :=
        E.mapDerivedCategory.preimageIso
          ((Functor.mapDerivedCategoryCompIso N E).symm.app L.obj ≪≫ eL)
      refine ⟨Lplus, L.property, ⟨?_⟩⟩
      exact DerivedCategory.TStructure.t.plus.isoMk
        (N.mapDerivedCategoryPlusCompatibility.app Lplus ≪≫ e)
    · intro B_e _hBe alpha
      let e : (finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj B_e.obj ≅ K :=
        (Functor.mapDerivedCategoryCompIso N E).app B_e.obj ≪≫
          E.mapDerivedCategory.mapIso
            ((N.mapDerivedCategoryPlusCompatibility.app B_e).symm ≪≫
              DerivedCategory.Plus.ι.mapIso alpha)
      have hv (i : ℤ) :
          IsZero ((DerivedCategory.homologyFunctor _ i).obj
            ((finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj B_e.obj)) ↔
          IsZero ((DerivedCategory.homologyFunctor _ i).obj K) :=
        (DerivedCategory.homologyFunctor _ i).mapIso e |>.isZero_iff
      constructor
      · have hi := hfinite.2.2.2 B_e.obj r s
        constructor
        · intro h
          refine ⟨hB, ?_⟩
          intro i hnz
          have hz (hout : i < r ∨ s < i) :
              IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
            apply (hv i).mp
            apply hi.mp ?_ i hout
            intro j hj
            rcases hj with hj | hj
            · exact (DerivedCategory.isGE_iff B_e.obj r).mp h.1 j hj
            · exact (DerivedCategory.isLE_iff B_e.obj s).mp h.2 j hj
          exact ⟨le_of_not_gt (fun h ↦ hnz (hz (Or.inl h))),
            le_of_not_gt (fun h ↦ hnz (hz (Or.inr h)))⟩
        · intro h
          have hz : ∀ i : ℤ, (i < r ∨ s < i) →
              IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
            intro i hi
            by_contra hnz
            have hb := h.2 hnz
            rcases hi with hi | hi
            · exact (not_lt_of_ge hb.1) hi
            · exact (not_lt_of_ge hb.2) hi
          have he := hi.mpr (fun i hi ↦ (hv i).mpr (hz i hi))
          exact ⟨(DerivedCategory.isGE_iff B_e.obj r).mpr
            (fun i hi ↦ he i (Or.inl hi)),
            (DerivedCategory.isLE_iff B_e.obj s).mpr (fun i hi ↦ he i (Or.inr hi))⟩
      · intro hTor
        apply (comparison_torAmplitudeIn_iff P.Ring T r s _hrs B_e).mpr
        let eB := E.mapDerivedCategory.mapIso (DerivedCategory.Plus.ι.mapIso alpha)
        refine ⟨hTor.1, ?_⟩
        intro L Q hL f hf hQ M i hi
        exact hTor.2 L Q (hL.map (fun eL ↦ eL ≪≫ eB)) f hf hQ M i hi
  · intro B _hB B_e _hBe alpha
    simp only [witnessTransportIdentification, Iso.trans_inv, Iso.symm_inv,
      Iso.app_inv, Functor.mapIso_hom]
    rw [hcomparison]
    rfl
  · intro B B' _hB _hB' B_e B'_e _hBe _hBe' alpha alpha' beta h hab
    let H := witnessTransportFunctor P.Coefficient T Z G
    let c := witnessTransportComparison P.Coefficient T Z G
    have he : H.map h ≫ H.map alpha'.inv =
        H.map alpha.inv ≫ H.map (N.mapDerivedCategoryPlus.map beta) := by
      apply (cancel_epi (H.map alpha.hom)).mp
      calc
        _ = H.map (alpha.hom ≫ h) ≫ H.map alpha'.inv := by
          rw [H.map_comp, Category.assoc]
        _ = H.map (N.mapDerivedCategoryPlus.map beta ≫ alpha'.hom) ≫
            H.map alpha'.inv := by rw [hab]
        _ = H.map (N.mapDerivedCategoryPlus.map beta) := by
          rw [H.map_comp, Category.assoc, ← H.map_comp, Iso.hom_inv_id,
            H.map_id, Category.comp_id]
        _ = _ := by
          rw [← Category.assoc, ← H.map_comp, Iso.hom_inv_id, H.map_id,
            Category.id_comp]
    change H.map h ≫ (H.map alpha'.inv ≫ c.hom.app B'_e) =
      (H.map alpha.inv ≫ c.hom.app B_e) ≫ _
    have hn := c.hom.naturality beta
    change H.map (N.mapDerivedCategoryPlus.map beta) ≫ c.hom.app B'_e = _ at hn
    rw [← Category.assoc, he, Category.assoc, hn, Category.assoc]

end AlgebraicGeometry.ProEtale
