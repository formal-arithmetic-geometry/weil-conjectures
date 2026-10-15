/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.UpperTruncationStepQuotient
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Sheaf.CategoryTheory.CartanEilenbergTotalResolution
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Sheaf.CategoryTheory.LeftExactTruncationIso

/-! # Smart truncations of Cartan--Eilenberg resolutions

Source: Stacks Project, Tags 015K and 015X.
(blueprint: lem-sp-ce-truncation-resolution).
-/

@[expose] public section
set_option autoImplicit false
universe uA vA uB vB uC vC
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {F : A ⥤ B} [F.Additive]

private theorem ce_truncLE_injective (P : CartanEilenbergPresentation F) (q p : ℤ) (r : ℕ) :
    Injective (((CochainComplex.truncLE P.I q).X p).X r) := by
  by_cases hp : p < q
  · exact Injective.of_iso
      ((HomologicalComplex.eval B (.up ℕ) r).mapIso (CochainComplex.truncLEXIso P.I q p hp)).symm
      (P.term_injective p r)
  · by_cases he : p = q
    · subst p
      exact Injective.of_iso
        ((HomologicalComplex.eval B (.up ℕ) r).mapIso (CochainComplex.truncLEXIsoCycles P.I q)).symm
        (P.horizontal_injective q r).1
    · have hz := (HomologicalComplex.eval B (.up ℕ) r).map_isZero
        ((CochainComplex.truncLE P.I q).isZero_of_isStrictlyLE q p (by omega))
      exact hz.injective

private theorem ce_truncLE_quasiIso (P : CartanEilenbergPresentation F) (q p : ℤ) :
    QuasiIso ((CochainComplex.truncLEMap P.e q).f p) := by
  let S := ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (P.J.cocomplex.extend ComplexShape.embeddingUpNat))
  let u := CochainComplex.truncLEMap P.e q
  have hw := congrArg (fun k ↦ k.f p) (CochainComplex.ιTruncLE_naturality P.e q)
  change u.f p ≫ (CochainComplex.ιTruncLE P.I q).f p =
    (CochainComplex.ιTruncLE S q).f p ≫ P.e.f p at hw
  by_cases hp : p < q
  · have hw' : u.f p ≫ (CochainComplex.truncLEXIso P.I q p hp).hom =
        (CochainComplex.truncLEXIso S q p hp).hom ≫ P.e.f p := by
      simpa only [(CochainComplex.truncLE_inclusion_coordinates P.I q).2 p hp,
        (CochainComplex.truncLE_inclusion_coordinates S q).2 p hp] using hw
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (CochainComplex.truncLEXIso S q p hp)
        (CochainComplex.truncLEXIso P.I q p hp) hw'.symm)).mpr (P.column_quasiIso p)
  · by_cases he : p = q
    · subst p
      have hw' : u.f q ≫ (CochainComplex.truncLEXIsoCycles P.I q).hom =
          (CochainComplex.truncLEXIsoCycles S q).hom ≫
            HomologicalComplex.cyclesMap P.e q := by
        apply (cancel_mono (P.I.iCycles q)).1
        rw [Category.assoc, (CochainComplex.truncLE_inclusion_coordinates P.I q).1,
          Category.assoc, HomologicalComplex.cyclesMap_i,
          ← Category.assoc, (CochainComplex.truncLE_inclusion_coordinates S q).1]
        exact hw
      exact (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk (CochainComplex.truncLEXIsoCycles S q)
          (CochainComplex.truncLEXIsoCycles P.I q) hw'.symm)).mpr (P.horizontal_quasiIso q).1
    · have hS := (CochainComplex.truncLE S q).isZero_of_isStrictlyLE q p (by omega)
      have hI := (CochainComplex.truncLE P.I q).isZero_of_isStrictlyLE q p (by omega)
      have : IsIso (u.f p) := IsZero.isIso hS hI _
      infer_instance


private theorem ce_truncLE_zero_neg (P : CartanEilenbergPresentation F) (q p : ℤ) (hp : p < 0) :
    IsZero ((CochainComplex.truncLE P.I q).X p) := by
  have : CochainComplex.IsStrictlyGE P.I 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact P.zero_neg
  have : CochainComplex.IsStrictlyGE (CochainComplex.truncLE P.I q) 0 := inferInstance
  exact (CochainComplex.truncLE P.I q).isZero_of_isStrictlyGE 0 p hp


set_option backward.isDefEq.respectTransparency false in
private theorem ce_truncLE_total_properties [IsGrothendieckAbelian.{vB} B]
    (P : CartanEilenbergPresentation F) (q : ℤ) :
    (∀ n : ℤ, Injective (((((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
        (CochainComplex.truncLE P.I q)).flip).total (ComplexShape.up ℤ)).X n)) ∧
      CochainComplex.IsStrictlyGE ((((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
        (CochainComplex.truncLE P.I q)).flip).total (ComplexShape.up ℤ)) 0 := by
  classical
  let I := CochainComplex.truncLE P.I q
  let J := ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip
  have hterms (s : ℤ) (r : ℕ) : Injective ((I.X s).X r) :=
    ce_truncLE_injective P q s r
  let b : ℤ := 0
  have hb (s : ℤ) (hs : s < b) : IsZero (I.X s) := ce_truncLE_zero_neg P q s hs
  have hz (r s : ℤ) (h : r < 0 ∨ s < b) : IsZero ((J.X r).X s) := by
    rcases h with h | h
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat r
        (fun m hm ↦ by change (m : ℤ) = r at hm; omega)
    · exact (HomologicalComplex.eval B (ComplexShape.up ℤ) r).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor B).map_isZero (hb s h))
  have hge : CochainComplex.IsStrictlyGE (J.total (ComplexShape.up ℤ)) b := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (K := J)
    intro r s hrs
    have hsum : r + s = n := hrs
    exact (hz r s (by omega)).eq_of_src _ _
  -- The full diagonal coproduct equals the coproduct of these finitely many summands.
  let κ (n : ℤ) : J.CoreHasTotal (ComplexShape.up ℤ) n :=
    { J := { s : ℤ // s ∈ Finset.Icc b n }
      φ₁ := fun s ↦ n - s
      φ₂ := fun s ↦ s
      π_φ := fun s ↦ by dsimp [ComplexShape.π]; omega
      hφ := by
        intro s t h
        apply Subtype.ext
        exact congrArg (fun x : ℤ × ℤ ↦ x.2) h
      isZero := by
        intro r s h hrs
        have hbounds : 0 ≤ r ∧ b ≤ s := by
          constructor <;> by_contra hbad
          · exact hrs (hz r s (Or.inl (by omega)))
          · exact hrs (hz r s (Or.inr (by omega)))
        refine ⟨⟨s, Finset.mem_Icc.mpr ⟨hbounds.2, ?_⟩⟩, ?_, rfl⟩
        · dsimp [ComplexShape.π] at h; omega
        · dsimp [ComplexShape.π] at h; dsimp; omega }
  let : HasFiniteBiproducts B := Abelian.hasFiniteBiproducts
  have hinj (n : ℤ) : Injective ((J.total (ComplexShape.up ℤ)).X n) := by
    let c := κ n
    let : Finite c.J := by dsimp [c, κ]; infer_instance
    let T : c.J → B := fun s ↦ (J.X (c.φ₁ s)).X (c.φ₂ s)
    have hi (s : c.J) : Injective (T s) := by
      have hr : 0 ≤ n - (s : ℤ) := by
        have := (Finset.mem_Icc.mp s.property).2
        omega
      let r := (n - (s : ℤ)).toNat
      have he : (r : ℤ) = n - (s : ℤ) := Int.toNat_of_nonneg hr
      exact Injective.of_iso
        (HomologicalComplex.extendXIso
          (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s))
          ComplexShape.embeddingUpNat (i := r) (i' := n - (s : ℤ)) he).symm
        (hterms s r)
    -- CoreHasTotal gives a genuine colimit, so no choice of an unproved witness is used.
    let e : (∐ T) ≅ (J.total (ComplexShape.up ℤ)).X n :=
      c.isColimit.coconePointUniqueUpToIso
        (J.toGradedObject.isColimitCofanMapObj
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)
    exact Injective.of_iso (biproduct.isoCoproduct T ≪≫ e) inferInstance
  exact ⟨hinj, hge⟩


private theorem comparison_comm (P Q : CartanEilenbergPresentation F)
    (d : P.Comparison Q) :
    P.e ≫ d.α = ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
      ((F.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap d.β ComplexShape.embeddingUpNat)) ≫ Q.e := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.Hom.ext
  funext r
  by_cases hr : r = 0
  · subst r
    simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      CochainComplex.single₀_map_f_zero] using d.comm_e p
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 _ r hr).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private theorem truncation_comparison_maps [IsGrothendieckAbelian.{vB} B]
    (P Q : CartanEilenbergPresentation F) (d : P.Comparison Q) (q : ℤ) :
    let K := fun R : CartanEilenbergPresentation F ↦
      (F.mapHomologicalComplex (.up ℤ)).obj
        (R.J.cocomplex.extend ComplexShape.embeddingUpNat)
    let I := fun R : CartanEilenbergPresentation F ↦ CochainComplex.truncLE R.I q
    let T := fun R : CartanEilenbergPresentation F ↦
      (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj (I R)
    let k := (F.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap d.β ComplexShape.embeddingUpNat)
    let u := CochainComplex.truncLEMap d.α q
    ∀ (aP : ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.truncLE (K P) q) ⟶ I P)
      (aQ : ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.truncLE (K Q) q) ⟶ I Q),
      aP ≫ CochainComplex.ιTruncLE P.I q =
        ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.ιTruncLE (K P) q) ≫ P.e →
      aQ ≫ CochainComplex.ιTruncLE Q.I q =
        ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.ιTruncLE (K Q) q) ≫ Q.e →
      aP ≫ u = ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.truncLEMap k q) ≫ aQ ∧
      ∀ (augP : CochainComplex.truncLE (K P) q ⟶ (T P).total (.up ℤ))
        (augQ : CochainComplex.truncLE (K Q) q ⟶ (T Q).total (.up ℤ)),
        (∀ n : ℤ, augP.f n = (aP.f n).f 0 ≫
          (HomologicalComplex.extendXIso
            (((𝟭 B).mapHomologicalComplex (.up ℕ)).obj ((I P).X n))
            ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
          (T P).ιTotal (.up ℤ) n 0 n (add_zero n)) →
        (∀ n : ℤ, augQ.f n = (aQ.f n).f 0 ≫
          (HomologicalComplex.extendXIso
            (((𝟭 B).mapHomologicalComplex (.up ℕ)).obj ((I Q).X n))
            ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
          (T Q).ιTotal (.up ℤ) n 0 n (add_zero n)) →
        augP ≫ HomologicalComplex₂.total.map
            ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).map u) (.up ℤ) =
          CochainComplex.truncLEMap k q ≫ augQ := by
  dsimp only
  intro aP aQ hP hQ
  have h : aP ≫ CochainComplex.truncLEMap d.α q =
      ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.truncLEMap
          ((F.mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.extendMap d.β ComplexShape.embeddingUpNat)) q) ≫ aQ := by
    have : Mono (CochainComplex.ιTruncLE Q.I q) :=
      inferInstanceAs (Mono (HomologicalComplex.ιTruncLE Q.I
        (ComplexShape.embeddingUpIntLE q)))
    apply (cancel_mono (CochainComplex.ιTruncLE Q.I q)).1
    rw [Category.assoc, CochainComplex.ιTruncLE_naturality, ← Category.assoc, hP,
      Category.assoc, comparison_comm P Q d, ← Category.assoc,
      ← Functor.map_comp, ← CochainComplex.ιTruncLE_naturality, Functor.map_comp,
      Category.assoc, ← hQ, ← Category.assoc]
  refine ⟨h, ?_⟩
  intro augP augQ hcP hcQ
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, hcP, hcQ]
  rw [Category.assoc, Category.assoc, HomologicalComplex₂.ιTotal_map]
  change (aP.f n).f 0 ≫ _ ≫
    (HomologicalComplex.extendMap ((CochainComplex.truncLEMap d.α q).f n)
      ComplexShape.embeddingUpNat).f 0 ≫ _ = _
  rw [HomologicalComplex.extendMap_f ((CochainComplex.truncLEMap d.α q).f n)
    ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hh := congrArg (fun z ↦ (z.f n).f 0) h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    CochainComplex.single₀_map_f_zero] at hh
  rw [← Category.assoc ((aP.f n).f 0), hh, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Horizontal smart truncation of a CE resolution is a bounded-below injective
resolution of the smart truncation of its augmented complex. Its unique augmentation
square and total coordinates specify the maps, so they can be used in a natural
comparison of truncation diagrams.
Source: Stacks Project, Tag 015K, Remark 13.21.4; Tag 015X, Remark 13.26.15.
(blueprint: lem-sp-ce-truncation-resolution).

Proof. Below q the truncated row is the original row, at q it is the horizontal
cycle row, and above q it is zero. The CE hypotheses give injectivity and a
quasi-isomorphism for every such row, including the boundary cycle row.
Putting a complex in resolution degree zero is exact, so its cycles commute
with this functor; the resulting coordinate isomorphisms identify the two
orders of smart truncation and augmentation. Naturality of the truncation
inclusion gives the displayed square. Both truncated complexes vanish in
negative horizontal degree. Apply the bounded-below augmented-total theorem
to these rows: its cone is acyclic, its total terms are finite sums of
injectives, and its total is bounded below. This supplies the stated
quasi-isomorphism, its coordinate formula, and K-injectivity. The total flip
isomorphism restores the original total convention; its sign is one on
resolution degree zero. The monic truncation inclusion determines a uniquely,
and the total coordinate formula determines aug uniquely. A presentation
comparison commutes with the original augmentation in every resolution degree:
in positive degrees its source is zero. Cancel the truncated inclusion to get
the truncated square. The total coordinate equations and naturality of total
summand inclusions then give the total augmentation square as well. -/
theorem cartanEilenberg_truncation_resolution [IsGrothendieckAbelian.{vB} B]
    (P : CartanEilenbergPresentation F) (q : ℤ) :
    let K := (F.mapHomologicalComplex (.up ℤ)).obj
      (P.J.cocomplex.extend ComplexShape.embeddingUpNat)
    let I := CochainComplex.truncLE P.I q
    let T := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I
    ∃! a : ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.truncLE K q) ⟶ I,
      a ≫ CochainComplex.ιTruncLE P.I q =
        ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.ιTruncLE K q) ≫ P.e ∧
      ∃! aug : CochainComplex.truncLE K q ⟶ T.total (.up ℤ),
        (∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
          (HomologicalComplex.extendXIso
            (((𝟭 B).mapHomologicalComplex (.up ℕ)).obj (I.X n))
            ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
          T.ιTotal (.up ℤ) n 0 n (add_zero n)) ∧
        QuasiIso aug ∧ (∀ n : ℤ, Injective ((T.total (.up ℤ)).X n)) ∧
        CochainComplex.IsStrictlyGE (T.total (.up ℤ)) 0 ∧
        CochainComplex.IsKInjective (T.total (.up ℤ)) ∧
        ∀ (Q : CartanEilenbergPresentation F) (d : P.Comparison Q),
          let KQ := (F.mapHomologicalComplex (.up ℤ)).obj
            (Q.J.cocomplex.extend ComplexShape.embeddingUpNat)
          let IQ := CochainComplex.truncLE Q.I q
          let TQ := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj IQ
          let k := (F.mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.extendMap d.β ComplexShape.embeddingUpNat)
          let u := CochainComplex.truncLEMap d.α q
          ∀ (aQ : ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).obj
              (CochainComplex.truncLE KQ q) ⟶ IQ),
            aQ ≫ CochainComplex.ιTruncLE Q.I q =
              ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
                (CochainComplex.ιTruncLE KQ q) ≫ Q.e →
            ∀ (augQ : CochainComplex.truncLE KQ q ⟶ TQ.total (.up ℤ)),
              (∀ n : ℤ, augQ.f n = (aQ.f n).f 0 ≫
                (HomologicalComplex.extendXIso
                  (((𝟭 B).mapHomologicalComplex (.up ℕ)).obj (IQ.X n))
                  ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
                TQ.ιTotal (.up ℤ) n 0 n (add_zero n)) →
              a ≫ u = ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
                  (CochainComplex.truncLEMap k q) ≫ aQ ∧
                aug ≫ HomologicalComplex₂.total.map
                    ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).map u) (.up ℤ) =
                  CochainComplex.truncLEMap k q ≫ augQ := by
  classical
  let K : CochainComplex B ℤ := (F.mapHomologicalComplex (.up ℤ)).obj
    (P.J.cocomplex.extend ComplexShape.embeddingUpNat)
  have : CochainComplex.IsStrictlyGE K 0 := by
    dsimp [K]
    infer_instance
  have : CochainComplex.IsStrictlyGE (CochainComplex.truncLE K q) 0 := inferInstance
  let K' : CochainComplex.Plus B := ⟨CochainComplex.truncLE K q, ⟨0, inferInstance⟩⟩
  obtain ⟨e, he, _⟩ := leftExact_truncation_iso (CochainComplex.single₀ B) K q
  let a := e.hom ≫ CochainComplex.truncLEMap P.e q
  have hrows (p : ℤ) : QuasiIso (a.f p) := by
    have : QuasiIso ((CochainComplex.truncLEMap P.e q).f p) := ce_truncLE_quasiIso P q p
    dsimp only [a, HomologicalComplex.comp_f]
    infer_instance
  have hcomm : a ≫ CochainComplex.ιTruncLE P.I q =
      ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.ιTruncLE K q) ≫ P.e := by
    dsimp only [a]
    rw [Category.assoc, CochainComplex.ιTruncLE_naturality, ← Category.assoc, he]
  refine ⟨a, ⟨hcomm, ?_⟩, ?_⟩
  · obtain ⟨aug, haug, hqi, hki⟩ := Functor.cartanEilenberg_total_resolution K'
      (CochainComplex.truncLE P.I q) a
      ⟨0, fun p hp ↦ ce_truncLE_zero_neg P q p hp⟩
      (fun p r ↦ ce_truncLE_injective P q p r) hrows
    let T := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
      (CochainComplex.truncLE P.I q)
    let eT := T.totalFlipIso (.up ℤ)
    have : QuasiIso aug := hqi
    have : CochainComplex.IsKInjective (T.flip.total (.up ℤ)) := hki
    have hc (n : ℤ) : (aug ≫ eT.hom).f n = (a.f n).f 0 ≫
        (HomologicalComplex.extendXIso
          (((𝟭 B).mapHomologicalComplex (.up ℕ)).obj ((CochainComplex.truncLE P.I q).X n))
          ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
        T.ιTotal (.up ℤ) n 0 n (add_zero n) := by
      dsimp only [HomologicalComplex.comp_f]
      rw [haug n]
      change ((a.f n).f 0 ≫ _ ≫ T.flip.ιTotal (.up ℤ) 0 n n (zero_add n)) ≫
        (T.totalFlipIso (.up ℤ)).hom.f n = _
      rw [Category.assoc, Category.assoc, HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
      simp only [ComplexShape.σ, TotalComplexShapeSymmetry.σ, mul_zero,
        Int.negOnePow_zero, one_smul]
    obtain ⟨hterms, hge⟩ := ce_truncLE_total_properties P q
    have : CochainComplex.IsStrictlyGE (T.flip.total (.up ℤ)) 0 := hge
    have ht (n : ℤ) : Injective ((T.total (.up ℤ)).X n) :=
      Injective.of_iso ((HomologicalComplex.eval B (.up ℤ) n).mapIso eT) (hterms n)
    refine ⟨aug ≫ eT.hom,
      ⟨hc, inferInstance, ht, CochainComplex.isStrictlyGE_of_iso eT 0,
        CochainComplex.isKInjective_of_iso eT, ?_⟩, ?_⟩
    · intro Q d
      dsimp only
      intro aQ hQ augQ hcQ
      have hn := truncation_comparison_maps P Q d q a aQ hcomm hQ
      exact ⟨hn.1, hn.2 _ _ hc hcQ⟩
    · intro aug' h'
      apply HomologicalComplex.Hom.ext
      funext n
      exact (h'.1 n).trans (hc n).symm
  · intro a' ha'
    have hm : Mono (CochainComplex.ιTruncLE P.I q) :=
      inferInstanceAs (Mono (HomologicalComplex.ιTruncLE P.I
        (ComplexShape.embeddingUpIntLE q)))
    apply (cancel_mono (CochainComplex.ιTruncLE P.I q)).1
    rw [ha'.1]
    dsimp only [a]
    rw [Category.assoc, CochainComplex.ιTruncLE_naturality, ← Category.assoc, he]

end CategoryTheory
