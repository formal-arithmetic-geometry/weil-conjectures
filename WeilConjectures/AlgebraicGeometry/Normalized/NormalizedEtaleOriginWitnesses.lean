/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginScalarComparisons
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginComparisonCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-!
# Compatible etale origins of normalized finite-coefficient towers

Source: blueprint main-20261015, proper base change,
prop-weil-pbc-preservation-constructible.proof.md, compatible witness sentence;
Stacks Project, proetale.tex, Tag 09B1, lemma-compare-derived (2)
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses).

The published fixed-ring presentation is used through its canonical coefficient
realization. Index n denotes the positive exponent n+1. No level is omitted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : Scheme.AdicCoefficientDatum A)
  (M : ∀ n : ℕ, PbcWitnessAmbient T d n)
  (hM : ∀ n : ℕ, DerivedCategory.TStructure.t.plus
    ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (M n)))
  (W : ∀ n : ℕ, Scheme.EtaleOriginWitness T (PbcQuotient d n)
    ⟨(finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (M n), hM n⟩)
  (rho : ∀ (m n : ℕ) (h : n ≤ m),
    (normalizedOriginReduction (Scheme.ProEt.topology T) d m n h).obj (M m) ≅ M n)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private theorem plus_of_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (K : DerivedCategory C)
    (hK : DerivedCategory.TStructure.t.plus (F.mapDerivedCategory.obj K)) :
    DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, ha⟩ := hK
  refine ⟨a, (DerivedCategory.isGE_iff K a).2 ?_⟩
  intro i hi
  exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    ((DerivedCategory.isGE_iff _ a).1 ha i hi)

/-- The required equation for a lift of a supplied normalization. Its source is
identified using the inverse of the canonical comparison-reduction mate.
Source: Stacks 07A4 and Tag 09B1, coefficient refinement of the blueprint's witness sentence
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
def NormalizedOriginCompatibility (m n : ℕ) (h : n ≤ m)
    (beta : (pbcFixedScalarExtension T.smallEtaleTopology
        (pbcWitnessQuotientMap d m n h)).obj (W m).L.obj ≅
      (W n).L.obj) : Prop :=
  (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
      beta.hom ≫ (pbcFixedOriginAlpha T (PbcQuotient d n) (M n) (hM n) (W n)).hom =
    (pbcComparisonReduction T (pbcWitnessQuotientMap d m n h)).inv.app (W m).L.obj ≫
      (pbcFixedScalarExtension (Scheme.ProEt.topology T) (pbcWitnessQuotientMap d m n h)).map
        (pbcFixedOriginAlpha T (PbcQuotient d m) (M m) (hM m) (W m)).hom ≫ (rho m n h).hom

private def comparisonNormalizationIso (m n : ℕ) (h : n ≤ m) :
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.obj
      ((pbcFixedScalarExtension T.smallEtaleTopology
        (pbcWitnessQuotientMap d m n h)).obj (W m).L.obj) ≅ M n :=
  (pbcComparisonReduction T (pbcWitnessQuotientMap d m n h)).symm.app (W m).L.obj ≪≫
    (pbcFixedScalarExtension (Scheme.ProEt.topology T) (pbcWitnessQuotientMap d m n h)).mapIso
      (pbcFixedOriginAlpha T (PbcQuotient d m) (M m) (hM m) (W m)) ≪≫ rho m n h

private theorem normalizedOrigin_bounded (m n : ℕ) (h : n ≤ m) :
    DerivedCategory.TStructure.t.plus
      ((pbcFixedScalarExtension T.smallEtaleTopology
        (pbcWitnessQuotientMap d m n h)).obj (W m).L.obj) := by
  apply plus_of_map (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T)
  apply plus_of_map (finiteCoefficientRealization T (PbcQuotient d n))
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.mapIso
      (comparisonNormalizationIso T d M hM W rho m n h)).symm (hM n)

private theorem normalizationLift (m n : ℕ) (h : n ≤ m) :
    ∃! beta : (pbcFixedScalarExtension T.smallEtaleTopology
        (pbcWitnessQuotientMap d m n h)).obj (W m).L.obj ≅
      (W n).L.obj, NormalizedOriginCompatibility T d M hM W rho m n h beta := by
  let C := (pbcFixedScalarExtension T.smallEtaleTopology
        (pbcWitnessQuotientMap d m n h)).obj (W m).L.obj
  let F := (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory
  have hC := normalizedOrigin_bounded T d M hM W rho m n h
  let e : F.obj C ≅ F.obj (W n).L.obj :=
    comparisonNormalizationIso T d M hM W rho m n h ≪≫
      (pbcFixedOriginAlpha T (PbcQuotient d n) (M n) (hM n) (W n)).symm
  obtain ⟨f, hf⟩ :=
    (bijective_comparisonUpperStar_mapDerivedCategory_map C (W n).L.obj (W n).L.property).2
      e.hom
  obtain ⟨g, hg⟩ :=
    (bijective_comparisonUpperStar_mapDerivedCategory_map (W n).L.obj C hC).2 e.inv
  change F.map f = e.hom at hf
  change F.map g = e.inv at hg
  have hfg : f ≫ g = 𝟙 C :=
    (bijective_comparisonUpperStar_mapDerivedCategory_map C C hC).1 (by
      change F.map (f ≫ g) = F.map (𝟙 C)
      simp only [Functor.map_comp, hf, hg, Iso.hom_inv_id]
      exact (F.map_id _).symm)
  have hgf : g ≫ f = 𝟙 (W n).L.obj :=
    (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ (W n).L.property).1 (by
      change F.map (g ≫ f) = F.map (𝟙 (W n).L.obj)
      simp only [Functor.map_comp, hf, hg, Iso.inv_hom_id]
      exact (F.map_id _).symm)
  let b : C ≅ (W n).L.obj := ⟨f, g, hfg, hgf⟩
  have hb : NormalizedOriginCompatibility T d M hM W rho m n h b := by
    change F.map f ≫ _ = _
    rw [hf]
    simp [e, comparisonNormalizationIso]
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply (bijective_comparisonUpperStar_mapDerivedCategory_map C _ (W n).L.property).1
  apply (cancel_mono
    (pbcFixedOriginAlpha T (PbcQuotient d n) (M n) (hM n) (W n)).hom).1
  exact hb'.trans hb.symm

/-- Chosen bounded-below etale origins lift every normalization uniquely, with unit
and quotient-cocycle compatibility. There is no common bound, constructibility, or
finite Tor-dimension assumption. The natural number n denotes P_(n+1).
Source: blueprint main-20261015, proper base change,
prop-weil-pbc-preservation-constructible.proof.md, compatible witness sentence;
Stacks Project Tag 09B1, lemma-compare-derived (2), with coefficient-reduction refinement
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses).

Proof: form the comparison-side normalization by composing the inverse canonical
comparison-reduction mate, the reduction of the retained origin isomorphism, and rho.
Its target is M_n. The coefficient realization and comparison inverse image are exact
and faithful, hence reflect vanishing cohomology. Transport boundedness of M_n along
this normalization and reflect it twice; the reduced etale object is bounded below.
The bound may depend on n. The existing comparison Hom bijection now lifts both the
normalization isomorphism and its inverse. Injectivity proves the inverse identities,
and cancellation of the retained origin isomorphism proves compatibility and uniqueness.
Choose these unique lifts for every pair of indices. For equal indices, the unit equation
of normalizedOriginComparisonCoherence, naturality of the scalar unit, and rho_id show
that their comparison images agree with the canonical scalar unit. For three indices,
use naturality of the inverse comparison-reduction mate to move the first lifted map
through the second comparison. Substitute both compatibility equations and rho_comp.
Naturality of the scalar associator and the composition equation of
normalizedOriginComparisonCoherence identify the result with the image of the direct
lift preceded by the etale associator. Cancel the retained origin isomorphism and apply
injectivity of the comparison Hom map. This proves the required unit and cocycle.
The independent coherence theorem isolates precisely the unit and associator part of
the argument; boundedness, existence, uniqueness and the descent of coherence are proved
here without a uniform bound, quotient flatness or a finite Tor-dimension hypothesis.
-/
theorem normalizedEtaleOriginWitnesses
    (rho_id : ∀ n : ℕ, (rho n n (le_refl n)).hom =
      (normalizedOriginScalarUnit (Scheme.ProEt.topology T)
        (pbcWitnessQuotientMap d n n (le_refl n))
        (Scheme.adicQuotientMap_id d.ideal ⟨n + 1, Nat.succ_pos n⟩)).hom.app (M n))
    (rho_comp : ∀ (k m n : ℕ) (hnm : n ≤ m) (hmk : m ≤ k),
      (pbcFixedScalarExtension (Scheme.ProEt.topology T) (pbcWitnessQuotientMap d m n hnm)).map
          (rho k m hmk).hom ≫ (rho m n hnm).hom =
        (pbcFixedScalarExtensionComp (Scheme.ProEt.topology T)
        (pbcWitnessQuotientMap d k m hmk)
        (pbcWitnessQuotientMap d m n hnm)
        (pbcWitnessQuotientMap d k n (hnm.trans hmk))
        (Scheme.adicQuotientMap_comp d.ideal ⟨k + 1, Nat.succ_pos k⟩
          ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
          (Nat.add_le_add_right hnm 1) (Nat.add_le_add_right hmk 1)).symm).hom.app
          (M k) ≫ (rho k n (hnm.trans hmk)).hom) :
    (∀ (m n : ℕ) (h : n ≤ m), DerivedCategory.TStructure.t.plus
      ((pbcFixedScalarExtension T.smallEtaleTopology
        (pbcWitnessQuotientMap d m n h)).obj (W m).L.obj)) ∧
    ∃ beta : ∀ (m n : ℕ) (h : n ≤ m),
        (pbcFixedScalarExtension T.smallEtaleTopology
        (pbcWitnessQuotientMap d m n h)).obj (W m).L.obj ≅
          (W n).L.obj,
      (∀ (m n : ℕ) (h : n ≤ m),
        NormalizedOriginCompatibility T d M hM W rho m n h (beta m n h)) ∧
      (∀ (m n : ℕ) (h : n ≤ m)
        (beta' : (pbcFixedScalarExtension T.smallEtaleTopology
        (pbcWitnessQuotientMap d m n h)).obj (W m).L.obj ≅
          (W n).L.obj),
        NormalizedOriginCompatibility T d M hM W rho m n h beta' → beta' = beta m n h) ∧
      (∀ n : ℕ, (beta n n (le_refl n)).hom =
        (normalizedOriginScalarUnit T.smallEtaleTopology
        (pbcWitnessQuotientMap d n n (le_refl n))
        (Scheme.adicQuotientMap_id d.ideal ⟨n + 1, Nat.succ_pos n⟩)).hom.app (W n).L.obj) ∧
      (∀ (k m n : ℕ) (hnm : n ≤ m) (hmk : m ≤ k),
        (pbcFixedScalarExtension T.smallEtaleTopology (pbcWitnessQuotientMap d m n hnm)).map
            (beta k m hmk).hom ≫ (beta m n hnm).hom =
          (pbcFixedScalarExtensionComp T.smallEtaleTopology
        (pbcWitnessQuotientMap d k m hmk)
        (pbcWitnessQuotientMap d m n hnm)
        (pbcWitnessQuotientMap d k n (hnm.trans hmk))
        (Scheme.adicQuotientMap_comp d.ideal ⟨k + 1, Nat.succ_pos k⟩
          ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
          (Nat.add_le_add_right hnm 1) (Nat.add_le_add_right hmk 1)).symm).hom.app
            (W k).L.obj ≫ (beta k n (hnm.trans hmk)).hom) := by
  classical
  choose beta hb hu using normalizationLift T d M hM W rho
  refine ⟨normalizedOrigin_bounded T d M hM W rho, beta, hb, hu, ?_, ?_⟩
  · intro n
    apply (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ (W n).L.property).1
    apply (cancel_mono
      (pbcFixedOriginAlpha T (PbcQuotient d n) (M n) (hM n) (W n)).hom).1
    dsimp only
    rw [hb n n (le_refl n),
      (normalizedOriginComparisonCoherence T d).1, Category.assoc, rho_id]
    congr 1
    exact (normalizedOriginScalarUnit (Scheme.ProEt.topology T)
        (pbcWitnessQuotientMap d n n (le_refl n))
        (Scheme.adicQuotientMap_id d.ideal ⟨n + 1, Nat.succ_pos n⟩)).hom.naturality _
  · intro k m n hnm hmk
    apply (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ (W n).L.property).1
    apply (cancel_mono
      (pbcFixedOriginAlpha T (PbcQuotient d n) (M n) (hM n) (W n)).hom).1
    dsimp only
    simp only [Functor.map_comp, Category.assoc]
    rw [hb m n hnm, hb k n (hnm.trans hmk)]
    have hn := (pbcComparisonReduction T (pbcWitnessQuotientMap d m n hnm)).inv.naturality
      (beta k m hmk).hom
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    rw [← Functor.map_comp_assoc, hb k m hmk]
    simp only [Functor.map_comp, Category.assoc]
    rw [rho_comp]
    have ha :=
      (pbcFixedScalarExtensionComp (Scheme.ProEt.topology T)
        (pbcWitnessQuotientMap d k m hmk)
        (pbcWitnessQuotientMap d m n hnm)
        (pbcWitnessQuotientMap d k n (hnm.trans hmk))
        (Scheme.adicQuotientMap_comp d.ideal ⟨k + 1, Nat.succ_pos k⟩
          ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
          (Nat.add_le_add_right hnm 1) (Nat.add_le_add_right hmk 1)).symm).hom.naturality
      (pbcFixedOriginAlpha T (PbcQuotient d k) (M k) (hM k) (W k)).hom
    dsimp only [Functor.comp_map] at ha
    rw [reassoc_of% ha,
      ← reassoc_of% ((normalizedOriginComparisonCoherence T d).2 k m n hnm hmk (W k).L.obj)]

end AlgebraicGeometry.ProEtale
