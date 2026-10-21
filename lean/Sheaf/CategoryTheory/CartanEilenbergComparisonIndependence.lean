/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups E1 and N2
-/
module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredPageTwoModel
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import WeilConjectures.Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import all Sheaf.CategoryTheory.SecondFiltrationTwoColumnImage
import WeilConjectures.CategoryTheory.BoundedBelowSecondFiltration
import WeilConjectures.CategoryTheory.FilteredCohomologyImage
import WeilConjectures.CategoryTheory.DegreewiseFilteredStableQuotient
import Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy
import Sheaf.CategoryTheory.FilteredHomotopySpectralSequence
import Sheaf.Paper.CartanEilenbergLeftExactCohomology

/-! # Independence of Cartan--Eilenberg comparison maps

Source: Stacks Project, Derived Categories, Remarks and Lemmas 015K and 015N
(blueprint: lem-sp-cartan-eilenberg-comparison-independence).
-/

@[expose] public section

universe uAT vAT uBT vBT uCT vCT

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem filtration_ext
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    {X : C} (F G : DecreasingFiltration X) (h : ∀ p, F.step p = G.step p) : F = G := by
  cases F
  cases G
  congr
  exact funext h

private theorem model_convergence
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (M : FilteredPageTwoModel C) (U : FilteredObject (CochainComplex C ℤ))
    (hfinite : ∀ n : ℤ, ∃ lo hi : ℤ,
      U.filtration.complexStep lo n = ⊤ ∧ U.filtration.complexStep hi n = ⊥) :
    ∃ H : ∀ n : ℤ, DecreasingFiltration (U.obj.homology n),
      (∀ n : ℤ, (H n).IsFinite) ∧
      (∀ p n : ℤ, (H n).step p =
        imageSubobject (HomologicalComplex.homologyMap (U.filtration.step p).arrow n)) ∧
      (∀ p n : ℤ, ∃ (R : ℤ) (hR : 2 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
        Nonempty (((M.S.obj U).page r (le_trans hR hr)).X (p, n - p) ≅
          (H n).gradedPiece p)) := by
  obtain ⟨H, hfin, hstep, hstable⟩ := degreewiseFiltered_stable_quotient U.obj
    U.filtration hfinite (fun n ↦ U.obj.homology n) (fun _ ↦ Iso.refl _)
  have hstep' : ∀ p n : ℤ, (H n).step p =
      imageSubobject (HomologicalComplex.homologyMap (U.filtration.step p).arrow n) := by
    intro p n
    simpa only [Iso.refl_hom, Subobject.exists_iso_map, Subobject.map_id,
      Functor.id_obj] using hstep p n
  refine ⟨H, hfin, hstep', ?_⟩
  intro p n
  obtain ⟨R, hR, htail⟩ := hstable p n
  refine ⟨max 2 R, le_max_left _ _, ?_⟩
  intro r hr
  have hrR : R ≤ r := le_trans (le_max_right _ _) hr
  have hr2 : 2 ≤ r := le_trans (le_max_left _ _) hr
  obtain ⟨hBZ, ⟨e⟩⟩ := htail r hrR
  obtain ⟨ha, hb, φ, hφ, z, g, hz, hg, e', he'⟩ :=
    U.filtration.filteredComplex_quotient_image_comparison p n r (by omega) hBZ
  have hφ' : φ = M.φ U p r hr2 := by
    apply (cancel_epi (cokernel.π (Subobject.ofLE (U.filtration.step (p + r))
      (U.filtration.step p) (U.filtration.antitone_step (by omega))))).1
    exact hφ.trans (M.comm_φ U p r hr2).symm
  subst φ
  have ee : ((M.S.obj U).page r hr2).X (p, n - p) ≅
      image (HomologicalComplex.homologyMap (M.φ U p r hr2) n) := by
    have e₀ := M.pageIso U p (n - p) r hr2
    rw [show p + (n - p) = n by omega] at e₀
    exact e₀
  exact ⟨ee ≪≫ e'.symm ≪≫ e⟩

private def comparison_id
    {A : Type uAT} [Category.{vAT} A] [Abelian A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    {F : A ⥤ B} [F.Additive] (P : CartanEilenbergPresentation F) : P.Comparison P where
  f := 𝟙 P.X
  β := 𝟙 P.J.cocomplex
  α := 𝟙 P.I
  comm_ι := by simp
  comm_e p := by simp

private def comparison_comp
    {A : Type uAT} [Category.{vAT} A] [Abelian A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    {F : A ⥤ B} [F.Additive] {P Q R : CartanEilenbergPresentation F}
    (c : P.Comparison Q) (d : Q.Comparison R) : P.Comparison R where
  f := c.f ≫ d.f
  β := c.β ≫ d.β
  α := c.α ≫ d.α
  comm_ι := by
    simp only [HomologicalComplex.comp_f]
    rw [← Category.assoc, c.comm_ι, Category.assoc, d.comm_ι, ← Category.assoc]
  comm_e p := by
    simp only [HomologicalComplex.comp_f, HomologicalComplex.extendMap_comp,
      Functor.map_comp]
    rw [← Category.assoc, c.comm_e, Category.assoc, d.comm_e, ← Category.assoc]

private theorem finite_sup_hom_ext
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    {I : Type*} (s : Finset I) {A : I → C} {X Y : C} (a : ∀ i, A i ⟶ X)
    (g h : ((s.sup (fun i ↦ imageSubobject (a i)) : Subobject X) : C) ⟶ Y)
    (w : ∀ i, ∀ hi : i ∈ s,
      (factorThruImageSubobject (a i) ≫ Subobject.ofLE _ _
        (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)) ≫ g =
      (factorThruImageSubobject (a i) ≫ Subobject.ofLE _ _
        (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)) ≫ h) : g = h := by
  let S := s.sup (fun i ↦ imageSubobject (a i))
  let e := equalizer.ι g h ≫ S.arrow
  have hs : S ≤ Subobject.mk e := by
    apply Finset.sup_le
    intro i hi
    let l := factorThruImageSubobject (a i) ≫ Subobject.ofLE _ S
      (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)
    apply imageSubobject_le_mk e (a i) (equalizer.lift l (w i hi))
    simp [e, l]
  let r := Subobject.ofLE S (Subobject.mk e) hs ≫ (Subobject.underlyingIso e).hom
  have hr : r ≫ equalizer.ι g h = 𝟙 _ := by
    apply (cancel_mono S.arrow).1
    rw [Category.assoc, Category.id_comp]
    change r ≫ e = S.arrow
    simp [r]
  have : IsSplitEpi (equalizer.ι g h) := IsSplitEpi.mk' ⟨r, hr⟩
  exact (cancel_epi (equalizer.ι g h)).1 (equalizer.condition g h)

set_option backward.isDefEq.respectTransparency false in
private theorem second_step_retraction
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (p n : ℤ) :
    ∃ r : (K.total (ComplexShape.up ℤ)).X n ⟶ ((K.secondFiltration n).step p : C),
      ((K.secondFiltration n).step p).arrow ≫ r = 𝟙 _ ∧
      ∀ i j : ℤ, ∀ h : i + j = n,
        K.ιTotal (ComplexShape.up ℤ) i j n h ≫ r ≫
          ((K.secondFiltration n).step p).arrow =
        if j ∈ Finset.Icc p n then K.ιTotal (ComplexShape.up ℤ) i j n h else 0 := by
  classical
  let S := (K.secondFiltration n).step p
  have hgen (i j : ℤ) (h : i + j = n) (hj : j ∈ Finset.Icc p n) :
      imageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n h) ≤ S := by
    have h' := Finset.le_sup (f := fun k ↦ imageSubobject
      (K.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n)) hj
    have hi : n - j = i := by omega
    rw [hi, K.ιTotalOrZero_eq (ComplexShape.up ℤ) i j n h] at h'
    exact h'
  let r := K.totalDesc (fun i j h ↦
    if hj : j ∈ Finset.Icc p n then
      factorThruImageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n h) ≫
        Subobject.ofLE _ S (hgen i j h hj) else 0)
  have hr (i j : ℤ) (h : i + j = n) :
      K.ιTotal (ComplexShape.up ℤ) i j n h ≫ r ≫ S.arrow =
        if j ∈ Finset.Icc p n then K.ιTotal (ComplexShape.up ℤ) i j n h else 0 := by
    dsimp only [r]
    rw [K.ι_totalDesc_assoc]
    split_ifs <;> simp
  refine ⟨r, ?_, hr⟩
  change S.arrow ≫ r = 𝟙 _
  apply (cancel_mono S.arrow).1
  rw [Category.id_comp]
  apply finite_sup_hom_ext (Finset.Icc p n)
    (fun i ↦ K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n)
  intro i hi
  have hι : K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n =
      K.ιTotal (ComplexShape.up ℤ) (n - i) i n (by
        change (n - i) + i = n; omega) :=
    K.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - i) i n (by
      change (n - i) + i = n; omega)
  let l := factorThruImageSubobject
    (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n) ≫ Subobject.ofLE _ S
      (Finset.le_sup (f := fun k ↦ imageSubobject
        (K.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n)) hi)
  have hl : l ≫ S.arrow = K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n := by
    simp [l]
  change l ≫ ((S.arrow ≫ r) ≫ S.arrow) = l ≫ S.arrow
  calc
    l ≫ ((S.arrow ≫ r) ≫ S.arrow) =
        (l ≫ S.arrow) ≫ r ≫ S.arrow := by simp only [Category.assoc]
    _ = K.ιTotal (ComplexShape.up ℤ) (n - i) i n (by
        change (n - i) + i = n; omega) ≫ r ≫ S.arrow := by rw [hl, hι]
    _ = K.ιTotal (ComplexShape.up ℤ) (n - i) i n (by
        change (n - i) + i = n; omega) := by rw [hr, if_pos hi]
    _ = l ≫ S.arrow := (hl.trans hι).symm

private theorem first_quadrant_preserves_total
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (G : B ⥤ C) [G.Additive]
    (K : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hz : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) :
    G.PreservesTotalComplex K (ComplexShape.up ℤ) := by
  intro n
  let κ : K.CoreHasTotal (ComplexShape.up ℤ) n :=
    { J := {j : ℤ // j ∈ Finset.Icc 0 n}
      φ₁ := fun j ↦ n - j
      φ₂ := fun j ↦ j
      π_φ := fun j ↦ by dsimp [ComplexShape.π]; omega
      hφ := by
        intro j k h
        apply Subtype.ext
        exact congrArg (fun x : ℤ × ℤ ↦ x.2) h
      isZero := by
        intro i j h hn
        have hb : 0 ≤ i ∧ 0 ≤ j := by
          constructor <;> by_contra hbad
          · exact hn (hz i j (Or.inl (by omega)))
          · exact hn (hz i j (Or.inr (by omega)))
        refine ⟨⟨j, Finset.mem_Icc.mpr ⟨hb.2, ?_⟩⟩, ?_, rfl⟩
        · dsimp [ComplexShape.π] at h; omega
        · dsimp [ComplexShape.π] at h; dsimp; omega }
  exact κ.preserves G

set_option backward.isDefEq.respectTransparency false in
private theorem mapped_second_step
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (G : B ⥤ C) [G.Additive]
    (K : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] [G.PreservesTotalComplex K (ComplexShape.up ℤ)]
    (p n : ℤ) :
    let KG := (G.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K
    let S := (K.secondFiltration n).step p
    let T := (KG.secondFiltration n).step p
    let e := HomologicalComplex₂.mapTotalXIso G K (ComplexShape.up ℤ) n
    ∃ (a : (T : C) ⟶ G.obj (S : B)) (b : G.obj (S : B) ⟶ (T : C)),
      a ≫ G.map S.arrow = T.arrow ≫ e.hom ∧
      b ≫ T.arrow = G.map S.arrow ≫ e.inv := by
  classical
  dsimp only
  let KG := (G.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K
  let S := (K.secondFiltration n).step p
  let T := (KG.secondFiltration n).step p
  let e := HomologicalComplex₂.mapTotalXIso G K (ComplexShape.up ℤ) n
  obtain ⟨r, hr, hgen⟩ := second_step_retraction K p n
  obtain ⟨r', hr', hgen'⟩ := second_step_retraction KG p n
  have hproj : e.hom ≫ G.map (r ≫ S.arrow) = r' ≫ T.arrow ≫ e.hom := by
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    change KG.ιTotal (ComplexShape.up ℤ) i j n hij ≫
      e.hom ≫ G.map (r ≫ S.arrow) =
        KG.ιTotal (ComplexShape.up ℤ) i j n hij ≫ r' ≫ T.arrow ≫ e.hom
    calc
      _ = G.map (K.ιTotal (ComplexShape.up ℤ) i j n hij ≫ r ≫ S.arrow) := by
        rw [← Category.assoc, HomologicalComplex₂.ι_mapTotalXIso_hom, ← G.map_comp]
      _ = G.map (if j ∈ Finset.Icc p n then
          K.ιTotal (ComplexShape.up ℤ) i j n hij else 0) := by rw [hgen]
      _ = (if j ∈ Finset.Icc p n then
          KG.ιTotal (ComplexShape.up ℤ) i j n hij else 0) ≫ e.hom := by
        split_ifs with hj
        · exact (HomologicalComplex₂.ι_mapTotalXIso_hom G K (ComplexShape.up ℤ)
            i j n hij).symm
        · simp
      _ = _ := by rw [← hgen']; simp only [Category.assoc]; rfl
  let a := T.arrow ≫ e.hom ≫ G.map r
  let b := G.map S.arrow ≫ e.inv ≫ r'
  refine ⟨a, b, ?_, ?_⟩
  · dsimp only [a]
    rw [Category.assoc, Category.assoc, ← G.map_comp, hproj,
      ← Category.assoc, ← Category.assoc, hr', Category.id_comp]
  · have : IsSplitEpi (G.map r) := IsSplitEpi.mk' ⟨G.map S.arrow, by
      rw [← G.map_comp, hr, G.map_id]⟩
    have hproj' : G.map (r ≫ S.arrow) ≫ e.inv = e.inv ≫ r' ≫ T.arrow := by
      apply (cancel_epi e.hom).1
      rw [← Category.assoc, hproj, Category.assoc]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    apply (cancel_epi (G.map r)).1
    change G.map r ≫ (G.map S.arrow ≫ e.inv ≫ r') ≫ T.arrow =
      G.map r ≫ G.map S.arrow ≫ e.inv
    calc
      _ = (G.map (r ≫ S.arrow) ≫ e.inv) ≫ r' ≫ T.arrow := by
        simp only [G.map_comp, Category.assoc]
      _ = e.inv ≫ r' ≫ T.arrow ≫ r' ≫ T.arrow := by
        rw [hproj']; simp only [Category.assoc]
      _ = e.inv ≫ r' ≫ T.arrow := by
        rw [← Category.assoc T.arrow, hr', Category.id_comp]
      _ = _ := by rw [← hproj', G.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem total_homotopy_map
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (G : B ⥤ C) [G.Additive]
    (K L : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    [G.PreservesTotalComplex K (ComplexShape.up ℤ)]
    [G.PreservesTotalComplex L (ComplexShape.up ℤ)]
    (φ ψ : K ⟶ L)
    (H : Homotopy (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ))
      (HomologicalComplex₂.total.map ψ (ComplexShape.up ℤ)))
    (hH : ∀ p n : ℤ, ∃ a : ((K.secondFiltration n).step p : B) ⟶
        ((L.secondFiltration (n - 1)).step (p - 1) : B),
      a ≫ ((L.secondFiltration (n - 1)).step (p - 1)).arrow =
        ((K.secondFiltration n).step p).arrow ≫ H.hom n (n - 1)) :
    let KG : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
      (G.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K
    let LG : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
      (G.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj L
    ∃ H' : Homotopy
      (HomologicalComplex₂.total.map
        ((G.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map φ)
          (ComplexShape.up ℤ))
      (HomologicalComplex₂.total.map
        ((G.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map ψ)
          (ComplexShape.up ℤ)),
      ∀ p n : ℤ, ∃ a : ((KG.secondFiltration n).step p : C) ⟶
          ((LG.secondFiltration (n - 1)).step (p - 1) : C),
        a ≫ ((LG.secondFiltration (n - 1)).step (p - 1)).arrow =
          ((KG.secondFiltration n).step p).arrow ≫ H'.hom n (n - 1) := by
  let eK := HomologicalComplex₂.mapTotalIso G K (ComplexShape.up ℤ)
  let eL := HomologicalComplex₂.mapTotalIso G L (ComplexShape.up ℤ)
  let H' := ((G.mapHomotopy H).compLeft eK.hom).compRight eL.inv
  have hφ (f : K ⟶ L) :
      (eK.hom ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex₂.total.map f (ComplexShape.up ℤ))) ≫ eL.inv =
      HomologicalComplex₂.total.map
        ((G.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f)
          (ComplexShape.up ℤ) := by
    rw [← HomologicalComplex₂.mapTotalIso_hom_naturality]
    simp only [eL, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let KG : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    (G.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K
  let LG : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    (G.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj L
  have hh : ∃ H'' : Homotopy
      ((eK.hom ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ))) ≫ eL.inv)
      ((eK.hom ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex₂.total.map ψ (ComplexShape.up ℤ))) ≫ eL.inv),
      ∀ p n : ℤ, ∃ a : ((KG.secondFiltration n).step p : C) ⟶
          ((LG.secondFiltration (n - 1)).step (p - 1) : C),
        a ≫ ((LG.secondFiltration (n - 1)).step (p - 1)).arrow =
          ((KG.secondFiltration n).step p).arrow ≫ H''.hom n (n - 1) := by
    refine ⟨H', ?_⟩
    intro p n
    obtain ⟨a, ha⟩ := hH p n
    obtain ⟨aK, bK, haK, hbK⟩ := mapped_second_step G K p n
    obtain ⟨aL, bL, haL, hbL⟩ := mapped_second_step G L (p - 1) (n - 1)
    refine ⟨aK ≫ G.map a ≫ bL, ?_⟩
    simp only [H', Homotopy.compLeft_hom, Homotopy.compRight_hom,
      Functor.mapHomotopy_hom, Category.assoc]
    change _ = _ ≫
      (HomologicalComplex₂.mapTotalXIso G K (ComplexShape.up ℤ) n).hom ≫
      G.map (H.hom n (n - 1)) ≫
      (HomologicalComplex₂.mapTotalXIso G L (ComplexShape.up ℤ) (n - 1)).inv
    rw [hbL, ← Category.assoc (G.map a),
      ← G.map_comp, ha, G.map_comp]
    simp only [← Category.assoc]
    rw [haK]
  rw [hφ φ, hφ ψ] at hh
  exact hh

private theorem second_step_map
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (φ : K ⟶ L) (p n : ℤ) :
    ∃ f : ((K.secondFiltration n).step p : C) ⟶ ((L.secondFiltration n).step p : C),
      f ≫ ((L.secondFiltration n).step p).arrow =
        ((K.secondFiltration n).step p).arrow ≫
          (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f n := by
  classical
  let g := (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f n
  let Q := (L.secondFiltration n).step p
  let P := (Subobject.pullback g).obj Q
  have h : (K.secondFiltration n).step p ≤ P := by
    change (Finset.Icc p n).sup _ ≤ P
    apply Finset.sup_le
    intro i hi
    let a := K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n
    have hQ : Q.Factors (a ≫ g) := by
      dsimp [a, g]
      rw [HomologicalComplex₂.ιTotalOrZero_map]
      change Subobject.Factors ((Finset.Icc p n).sup
        (fun j ↦ imageSubobject (L.ιTotalOrZero (ComplexShape.up ℤ) (n - j) j n))) _
      apply Subobject.finset_sup_factors
      exact ⟨i, hi, imageSubobject_factors_comp_self _ _⟩
    have hP : P.Factors a := pullback_factors g Q a hQ
    exact imageSubobject_le a (P.factorThru a hP) (P.factorThru_arrow a hP)
  have hP := Subobject.factors_of_le ((K.secondFiltration n).step p).arrow h
    (Subobject.factors_self _)
  have hQ := (pullback_factors_iff g Q _).mp hP
  exact ⟨Q.factorThru _ hQ, Q.factorThru_arrow _ hQ⟩

private theorem total_homotopy_iso
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (K L K' L' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    [K'.HasTotal (ComplexShape.up ℤ)] [L'.HasTotal (ComplexShape.up ℤ)]
    (eK : K' ≅ K) (eL : L' ≅ L) (φ ψ : K ⟶ L)
    (H : Homotopy (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ))
      (HomologicalComplex₂.total.map ψ (ComplexShape.up ℤ)))
    (hH : ∀ p n : ℤ, ∃ a : ((K.secondFiltration n).step p : C) ⟶
        ((L.secondFiltration (n - 1)).step (p - 1) : C),
      a ≫ ((L.secondFiltration (n - 1)).step (p - 1)).arrow =
        ((K.secondFiltration n).step p).arrow ≫ H.hom n (n - 1)) :
    ∃ H' : Homotopy
      (HomologicalComplex₂.total.map (eK.hom ≫ φ ≫ eL.inv) (ComplexShape.up ℤ))
      (HomologicalComplex₂.total.map (eK.hom ≫ ψ ≫ eL.inv) (ComplexShape.up ℤ)),
      ∀ p n : ℤ, ∃ a : ((K'.secondFiltration n).step p : C) ⟶
          ((L'.secondFiltration (n - 1)).step (p - 1) : C),
        a ≫ ((L'.secondFiltration (n - 1)).step (p - 1)).arrow =
          ((K'.secondFiltration n).step p).arrow ≫ H'.hom n (n - 1) := by
  let u := HomologicalComplex₂.total.map eK.hom (ComplexShape.up ℤ)
  let v := HomologicalComplex₂.total.map eL.inv (ComplexShape.up ℤ)
  let H' := (H.compLeft u).compRight v
  have hh : ∃ H'' : Homotopy
      ((u ≫ HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)) ≫ v)
      ((u ≫ HomologicalComplex₂.total.map ψ (ComplexShape.up ℤ)) ≫ v),
      ∀ p n : ℤ, ∃ a : ((K'.secondFiltration n).step p : C) ⟶
          ((L'.secondFiltration (n - 1)).step (p - 1) : C),
        a ≫ ((L'.secondFiltration (n - 1)).step (p - 1)).arrow =
          ((K'.secondFiltration n).step p).arrow ≫ H''.hom n (n - 1) := by
    refine ⟨H', ?_⟩
    intro p n
    obtain ⟨a, ha⟩ := second_step_map K' K eK.hom p n
    obtain ⟨b, hb⟩ := hH p n
    obtain ⟨c, hc⟩ := second_step_map L L' eL.inv (p - 1) (n - 1)
    refine ⟨a ≫ b ≫ c, ?_⟩
    simp only [H', Homotopy.compLeft_hom, Homotopy.compRight_hom,
      Category.assoc, hc, reassoc_of% hb]
    rw [← Category.assoc, ← Category.assoc, ha]
    simp only [u, v, Category.assoc]
  have hφ (f : K ⟶ L) :
      ((u ≫ HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) ≫ v) =
        HomologicalComplex₂.total.map (eK.hom ≫ f ≫ eL.inv) (ComplexShape.up ℤ) := by
    simp only [u, v, HomologicalComplex₂.total.map_comp, Category.assoc]
  rw [hφ φ, hφ ψ] at hh
  exact hh

private theorem comparison_native_homotopy
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B] [IsGrothendieckAbelian.{vBT} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (P Q : CartanEilenbergPresentation F) (c c' : P.Comparison Q) (hc : c.f = c'.f) :
    let E := (ComplexShape.embeddingUpNat.extendFunctor B).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∃ H : Homotopy
      (HomologicalComplex₂.total.map (E.map c.α) (ComplexShape.up ℤ))
      (HomologicalComplex₂.total.map (E.map c'.α) (ComplexShape.up ℤ)),
      ∀ p n : ℤ, ∃ a : ((HomologicalComplex₂.secondFiltration (E.obj P.I) n).step p : B) ⟶
        ((HomologicalComplex₂.secondFiltration (E.obj Q.I) (n - 1)).step (p - 1) : B),
        a ≫ ((HomologicalComplex₂.secondFiltration (E.obj Q.I) (n - 1)).step (p - 1)).arrow =
          ((HomologicalComplex₂.secondFiltration (E.obj P.I) n).step p).arrow ≫
            H.hom n (n - 1) := by
  classical
  let K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (P.J.cocomplex.extend ComplexShape.embeddingUpNat)
  let K' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (Q.J.cocomplex.extend ComplexShape.embeddingUpNat)
  have hcomm (d : P.Comparison Q) :
      P.J.ι ≫ d.β = (CochainComplex.single₀ A).map d.f ≫ Q.J.ι := by
    apply HomologicalComplex.from_single_hom_ext
    simpa only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] using d.comm_ι
  let hβ := InjectiveResolution.descHomotopy c.f c.β c'.β (hcomm c) (by
    rw [hc]
    exact hcomm c')
  let s := F.mapHomotopy (hβ.extend ComplexShape.embeddingUpNat)
  let w := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap c.β ComplexShape.embeddingUpNat) -
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap c'.β ComplexShape.embeddingUpNat)
  have hs (p : ℤ) : w.f p = s.hom p (p - 1) ≫ K'.d (p - 1) p +
      K.d p (p + 1) ≫ s.hom (p + 1) (p + 1 - 1) ≫
        eqToHom (congrArg K'.X (Int.add_sub_cancel p 1)) := by
    have h := (Homotopy.equivSubZero s).comm p
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)] at h
    simpa [Homotopy.equivSubZero, K, K', w, add_comm] using h
  have hδ (p : ℤ) : (P.e.f p).f 0 ≫ ((c.α - c'.α).f p).f 0 =
      w.f p ≫ (Q.e.f p).f 0 := by
    simp only [HomologicalComplex.sub_f_apply, Preadditive.comp_sub, w, Preadditive.sub_comp,
      c.comm_e p, c'.comm_e p]
  obtain ⟨tI, tJ, s1, s2, _, _, _, H, _, hH⟩ :=
    cartanEilenberg_doubleComplex_homotopy B K K' P.I Q.I P.e Q.e
      P.zero_neg Q.zero_neg P.horizontal_quasiIso Q.horizontal_quasiIso
      Q.horizontal_injective (c.α - c'.α) w (fun p ↦ s.hom p (p - 1)) hs hδ
  let E := (ComplexShape.embeddingUpNat.extendFunctor B).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have hm : HomologicalComplex₂.total.map (E.map (c.α - c'.α)) (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map (E.map c.α) (ComplexShape.up ℤ) -
        HomologicalComplex₂.total.map (E.map c'.α) (ComplexShape.up ℤ) := by
    rw [Functor.map_sub]
    ext1 n
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    simp only [HomologicalComplex.sub_f_apply, Preadditive.comp_sub,
      HomologicalComplex₂.ιTotal_map, Preadditive.sub_comp]
  have hh : ∃ H' : Homotopy
      (HomologicalComplex₂.total.map (E.map (c.α - c'.α)) (ComplexShape.up ℤ)) 0,
      ∀ p n : ℤ, ∃ a : ((HomologicalComplex₂.secondFiltration (E.obj P.I) n).step p : B) ⟶
        ((HomologicalComplex₂.secondFiltration (E.obj Q.I) (n - 1)).step (p - 1) : B),
        a ≫ ((HomologicalComplex₂.secondFiltration (E.obj Q.I) (n - 1)).step (p - 1)).arrow =
          ((HomologicalComplex₂.secondFiltration (E.obj P.I) n).step p).arrow ≫
            H'.hom n (n - 1) := ⟨H, hH⟩
  rw [hm] at hh
  obtain ⟨H', hH'⟩ := hh
  exact ⟨Homotopy.equivSubZero.symm H', hH'⟩

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_filtered_homotopy
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B] [IsGrothendieckAbelian.{vBT} B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C] [IsGrothendieckAbelian.{vCT} C]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (P Q : CartanEilenbergPresentation F) (c c' : P.Comparison Q)
    (hc : c.f = c'.f)
    (L : DecreasingFiltration (P.total G)) (L' : DecreasingFiltration (Q.total G))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      (((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)
    (hL' : ∀ p n : ℤ, L'.complexStep p n =
      (((CartanEilenbergPresentation.mappedFunctor G).obj Q.I).secondFiltration n).step p) :
    ∃ H : Homotopy
      (HomologicalComplex₂.total.map
        ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ))
      (HomologicalComplex₂.total.map
        ((CartanEilenbergPresentation.mappedFunctor G).map c'.α) (ComplexShape.up ℤ)),
      ∀ p n : ℤ, ∃ a : (L.complexStep p n : C) ⟶
        (L'.complexStep (p - 1) (n - 1) : C),
        a ≫ (L'.complexStep (p - 1) (n - 1)).arrow =
          (L.complexStep p n).arrow ≫ H.hom n (n - 1) := by
  classical
  let E := (ComplexShape.embeddingUpNat.extendFunctor B).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let GP := G.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let EP : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) := E.obj P.I
  let EQ : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) := E.obj Q.I
  have hz (R : CartanEilenbergPresentation F) (i j : ℤ) (h : i < 0 ∨ j < 0) :
      IsZero (((E.obj R.I).X i).X j) := by
    rcases h with hi | hj
    · exact (HomologicalComplex.eval B (ComplexShape.up ℤ) j).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor B).map_isZero (R.zero_neg i hi))
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat j
        (by intro r; change (r : ℤ) ≠ j; omega)
  let := first_quadrant_preserves_total G EP (hz P)
  let := first_quadrant_preserves_total G EQ (hz Q)
  obtain ⟨H, hH⟩ := comparison_native_homotopy F P Q c c' hc
  obtain ⟨HG, hHG⟩ := total_homotopy_map G EP EQ (E.map c.α) (E.map c'.α) H hH
  let j := NatIso.mapHomologicalComplex
    (ComplexShape.embeddingUpNat.mapExtendFunctorNatIso G) (ComplexShape.up ℤ)
  let eP : (CartanEilenbergPresentation.mappedFunctor G).obj P.I ≅ GP.obj EP :=
    (j.app P.I).symm
  let eQ : (CartanEilenbergPresentation.mappedFunctor G).obj Q.I ≅ GP.obj EQ :=
    (j.app Q.I).symm
  have he (d : P.Comparison Q) :
      eP.hom ≫ GP.map (E.map d.α) ≫ eQ.inv =
        (CartanEilenbergPresentation.mappedFunctor G).map d.α := by
    change j.inv.app P.I ≫ GP.map (E.map d.α) ≫ j.hom.app Q.I = _
    have hn : (CartanEilenbergPresentation.mappedFunctor G).map d.α ≫ j.inv.app Q.I =
        j.inv.app P.I ≫ GP.map (E.map d.α) := j.inv.naturality d.α
    rw [← Category.assoc, ← hn, Category.assoc]
    rw [Iso.inv_hom_id_app]
    exact Category.comp_id _
  obtain ⟨H', hH'⟩ := total_homotopy_iso (GP.obj EP) (GP.obj EQ)
    ((CartanEilenbergPresentation.mappedFunctor G).obj P.I)
    ((CartanEilenbergPresentation.mappedFunctor G).obj Q.I)
    eP eQ (GP.map (E.map c.α)) (GP.map (E.map c'.α)) HG hHG
  have hh : ∃ H'' : Homotopy
      (HomologicalComplex₂.total.map (eP.hom ≫ GP.map (E.map c.α) ≫ eQ.inv)
        (ComplexShape.up ℤ))
      (HomologicalComplex₂.total.map (eP.hom ≫ GP.map (E.map c'.α) ≫ eQ.inv)
        (ComplexShape.up ℤ)),
      ∀ p n : ℤ, ∃ a : (L.complexStep p n : C) ⟶
          (L'.complexStep (p - 1) (n - 1) : C),
        a ≫ (L'.complexStep (p - 1) (n - 1)).arrow =
          (L.complexStep p n).arrow ≫ H''.hom n (n - 1) := by
    refine ⟨H', ?_⟩
    intro p n
    rw [hL, hL']
    exact hH' p n
  rw [he c, he c'] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
private theorem map_cycle_lift_isIso
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (K : CochainComplex B ℤ) (q : ℤ) :
    IsIso (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).liftCycles
      (G.map (K.iCycles q)) (q + 1) (by simp) (by simp [← G.map_comp])) := by
  let KG := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let hk := isLimitForkMapOfIsLimit' G (K.iCycles_d q (q + 1))
    (K.cyclesIsKernel q (q + 1) (by simp))
  let e : G.obj (K.cycles q) ≅ KG.cycles q :=
    hk.conePointUniqueUpToIso (KG.cyclesIsKernel q (q + 1) (by simp))
  have he : e.hom = KG.liftCycles (G.map (K.iCycles q)) (q + 1) (by simp)
      (by simp [KG, ← G.map_comp]) := by
    apply (cancel_mono (KG.iCycles q)).1
    rw [HomologicalComplex.liftCycles_i]
    exact hk.conePointUniqueUpToIso_hom_comp _ WalkingParallelPair.zero
  rw [← he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_cohomology_naturality
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q : ℤ)
    (eK : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology q ≅
      G.obj (K.homology q))
    (eL : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology q ≅
      G.obj (L.homology q))
    (hK : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).liftCycles
        (G.map (K.iCycles q)) (q + 1) (by simp) (by simp [← G.map_comp]) ≫
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q ≫ eK.hom =
        G.map (K.homologyπ q))
    (hL : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).liftCycles
        (G.map (L.iCycles q)) (q + 1) (by simp) (by simp [← G.map_comp]) ≫
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homologyπ q ≫ eL.hom =
        G.map (L.homologyπ q)) :
    HomologicalComplex.homologyMap ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) q ≫
        eL.hom = eK.hom ≫ G.map (HomologicalComplex.homologyMap f q) := by
  let KG := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let LG := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let fG := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map f
  let a := KG.liftCycles (G.map (K.iCycles q)) (q + 1) (by simp)
    (by simp [KG, ← G.map_comp])
  let b := LG.liftCycles (G.map (L.iCycles q)) (q + 1) (by simp)
    (by simp [LG, ← G.map_comp])
  have : IsIso a := map_cycle_lift_isIso G K q
  have hab : a ≫ HomologicalComplex.cyclesMap fG q =
      G.map (HomologicalComplex.cyclesMap f q) ≫ b := by
    apply (cancel_mono (LG.iCycles q)).1
    dsimp only [a, b, fG, KG, LG]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
    change G.map (K.iCycles q) ≫ G.map (f.f q) =
      G.map (HomologicalComplex.cyclesMap f q) ≫ G.map (L.iCycles q)
    simp only [← G.map_comp, HomologicalComplex.cyclesMap_i]
  apply (cancel_epi (a ≫ KG.homologyπ q)).1
  calc
    _ = a ≫ HomologicalComplex.cyclesMap fG q ≫ LG.homologyπ q ≫ eL.hom := by
      dsimp only [KG, LG, fG]
      simp only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
    _ = G.map (HomologicalComplex.cyclesMap f q) ≫ G.map (L.homologyπ q) := by
      rw [← Category.assoc, ← Category.assoc, hab]
      simpa only [Category.assoc] using congrArg
        (fun t ↦ G.map (HomologicalComplex.cyclesMap f q) ≫ t) hL
    _ = G.map (K.homologyπ q) ≫ G.map (HomologicalComplex.homologyMap f q) := by
      rw [← G.map_comp, ← HomologicalComplex.homologyπ_naturality, G.map_comp]
    _ = _ := by
      rw [← hK]
      simp only [a, KG, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem exact_homology_projection
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (G : B ⥤ C) [G.Additive] [G.PreservesHomology]
    (I : CochainComplex B ℤ) (q : ℤ) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homologyπ q ≫
      ((I.sc q).mapHomologyIso G).hom =
        ((I.sc q).mapCyclesIso G).hom ≫ G.map (I.homologyπ q) := by
  exact ShortComplex.homologyπ_mapHomologyIso_hom G (I.sc q)

set_option backward.isDefEq.respectTransparency false in
private theorem mapped_horizontal_cohomology
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hbelow : ∀ k : ℤ, k < 0 → IsZero (I.X k))
    (hinj : ∀ (q : ℤ) (j : ℕ), Injective ((I.cycles q).X j) ∧
      Injective ((image (I.d (q - 1) q)).X j)) (q : ℤ) :
    let H := G.mapHomologicalComplex (ComplexShape.up ℕ)
    let J := (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
    ∃ e : J.homology q ≅ H.obj (I.homology q),
      J.liftCycles (H.map (I.iCycles q)) (q + 1) (by simp)
          (by simp [J, ← H.map_comp]) ≫ J.homologyπ q ≫ e.hom =
        H.map (I.homologyπ q) := by
  classical
  let H := G.mapHomologicalComplex (ComplexShape.up ℕ)
  let J := (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let a := J.liftCycles (H.map (I.iCycles q)) (q + 1) (by simp)
    (by simp [J, ← H.map_comp])
  have : IsIso a := map_cycle_lift_isIso H I q
  let f := a ≫ J.homologyπ q
  let g := H.map (I.homologyπ q)
  have hcomponents (j : ℕ) : ∃ e : (J.homology q).X j ≅ (H.obj (I.homology q)).X j,
      f.f j ≫ e.hom = g.f j := by
    let V := HomologicalComplex.eval B (ComplexShape.up ℕ) j
    let W := HomologicalComplex.eval C (ComplexShape.up ℕ) j
    let R := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
    let RG := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj R
    have hbounded : ∃ b : ℤ, ∀ k : ℤ, k < b → IsZero (R.X k) :=
      ⟨0, fun k hk ↦ V.map_isZero (hbelow k hk)⟩
    have hcycles (k : ℤ) : Injective (R.cycles k) :=
      Injective.of_iso ((I.sc k).mapCyclesIso V).symm (hinj k j).1
    have hboundaries (k : ℤ) : Injective (image (R.d (k - 1) k)) :=
      Injective.of_iso (PreservesImage.iso V (I.d (k - 1) k)).symm (hinj k j).2
    obtain ⟨eR, heR⟩ := cartanEilenberg_leftExact_cohomology R hbounded hcycles hboundaries G q
    let eB := (I.sc q).mapHomologyIso V
    let eC := (J.sc q).mapHomologyIso W
    let zB := (I.sc q).mapCyclesIso V
    let zC := (J.sc q).mapCyclesIso W
    let b := RG.liftCycles (G.map (R.iCycles q)) (q + 1) (by simp)
      (by simp [RG, ← G.map_comp])
    let e : (J.homology q).X j ≅ (H.obj (I.homology q)).X j :=
      eC.symm ≪≫ eR ≪≫ G.mapIso eB
    have hc : G.map zB.hom ≫ a.f j = b ≫ zC.hom := by
      apply (cancel_mono ((J.iCycles q).f j)).1
      rw [Category.assoc]
      have ha := congrArg (fun t ↦ t.f j)
        (HomologicalComplex.liftCycles_i J (H.map (I.iCycles q)) (q + 1) (by simp)
          (by simp [J, ← H.map_comp]))
      simp only [HomologicalComplex.comp_f] at ha
      rw [ha]
      change G.map zB.hom ≫ G.map ((I.iCycles q).f j) = _
      rw [← G.map_comp]
      have hzB : zB.hom ≫ (I.iCycles q).f j = R.iCycles q :=
        (I.sc q).mapCyclesIso_hom_iCycles V
      have hzC : zC.hom ≫ (J.iCycles q).f j = RG.iCycles q :=
        (J.sc q).mapCyclesIso_hom_iCycles W
      rw [Category.assoc, hzC, HomologicalComplex.liftCycles_i]
      exact congrArg G.map hzB
    refine ⟨e, ?_⟩
    apply (cancel_epi (G.map zB.hom)).1
    have hB : R.homologyπ q ≫ eB.hom = zB.hom ≫ (I.homologyπ q).f j :=
      exact_homology_projection V I q
    have hC : RG.homologyπ q ≫ eC.hom = zC.hom ≫ (J.homologyπ q).f j :=
      exact_homology_projection W J q
    calc
      _ = (G.map zB.hom ≫ a.f j) ≫ (J.homologyπ q).f j ≫
          eC.inv ≫ eR.hom ≫ G.map eB.hom := by
        simp only [f, e, HomologicalComplex.comp_f, Iso.trans_hom, Iso.symm_hom,
          Functor.mapIso_hom, Category.assoc]
      _ = b ≫ RG.homologyπ q ≫ eR.hom ≫ G.map eB.hom := by
        rw [hc]
        simp only [Category.assoc]
        rw [← reassoc_of% hC]
        simp only [Iso.hom_inv_id_assoc]
      _ = G.map (R.homologyπ q) ≫ G.map eB.hom := by
        simpa only [b, RG, Category.assoc] using
          congrArg (fun t ↦ t ≫ G.map eB.hom) heR
      _ = _ := by
        rw [← G.map_comp, hB, G.map_comp]
        rfl
  choose e he using hcomponents
  have hf (j : ℕ) : Epi (f.f j) := by
    change Epi ((HomologicalComplex.eval C (ComplexShape.up ℕ) j).map f)
    infer_instance
  let e' : J.homology q ≅ H.obj (I.homology q) :=
    HomologicalComplex.Hom.isoOfComponents e (by
      intro j k hjk
      apply (cancel_epi (f.f j)).1
      calc
        _ = g.f j ≫ (H.obj (I.homology q)).d j k := by rw [← Category.assoc, he j]
        _ = (H.obj (I.cycles q)).d j k ≫ g.f k := g.comm j k
        _ = _ := by rw [← he k, ← Category.assoc, ← f.comm j k, Category.assoc])
  refine ⟨e', ?_⟩
  have he' : f ≫ e'.hom = g := by
    ext j
    simpa only [e', HomologicalComplex.comp_f,
      HomologicalComplex.Hom.isoOfComponents_hom_f] using he j
  simpa only [f, a, g, H, J, Category.assoc] using he'

set_option backward.isDefEq.respectTransparency false in
private theorem presentation_horizontal_cohomology
    {A : Type uAT} [Category.{vAT} A] [Abelian A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (F : A ⥤ B) [F.Additive]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] :
    let H := G.mapHomologicalComplex (ComplexShape.up ℕ)
    ∃ e : ∀ (P : CartanEilenbergPresentation F) (q : ℤ),
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj P.I).homology q ≅
          H.obj (P.I.homology q),
      ∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (q : ℤ),
        HomologicalComplex.homologyMap
            ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map c.α) q ≫
          (e Q q).hom = (e P q).hom ≫ H.map (HomologicalComplex.homologyMap c.α q) := by
  classical
  let H := G.mapHomologicalComplex (ComplexShape.up ℕ)
  have h (P : CartanEilenbergPresentation F) (q : ℤ) :=
    mapped_horizontal_cohomology G P.I P.zero_neg
      (fun k j ↦ ⟨(P.horizontal_injective k j).1, (P.horizontal_injective k j).2.1⟩) q
  choose e he using h
  refine ⟨e, ?_⟩
  intro P Q c q
  exact canonical_cohomology_naturality H c.α q (e P q) (e Q q) (he P q) (he Q q)

private noncomputable def presentation_base_iso
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] (P : CartanEilenbergPresentation F) (q : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (P.J.cocomplex.extend ComplexShape.embeddingUpNat)).homology (q : ℤ) ≅
        (F.rightDerived q).obj P.X :=
  (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (q : ℤ)).mapIso
      ((ComplexShape.embeddingUpNat.mapExtendFunctorNatIso F).app P.J.cocomplex) ≪≫
    HomologicalComplex.extendHomologyIso
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
      ComplexShape.embeddingUpNat rfl ≪≫ (P.J.isoRightDerivedObj F q).symm

private noncomputable def presentation_homology_resolution
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] (P : CartanEilenbergPresentation F) (q : ℕ) :
    InjectiveResolution (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (P.J.cocomplex.extend ComplexShape.embeddingUpNat)).homology (q : ℤ)) where
  cocomplex := P.I.homology (q : ℤ)
  injective := fun p ↦ (P.horizontal_injective (q : ℤ) p).2.2
  ι := (((CochainComplex.single₀ B).mapHomologicalComplexHomologyIso
      (ComplexShape.up ℤ) (q : ℤ)).app _).inv ≫
    HomologicalComplex.homologyMap P.e (q : ℤ)
  quasiIso := by
    have := (P.horizontal_quasiIso (q : ℤ)).2.2
    infer_instance

private theorem presentation_augmentation_naturality
    {A : Type uAT} [Category.{vAT} A] [Abelian A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] {P Q : CartanEilenbergPresentation F}
    (c : P.Comparison Q) :
    P.e ≫ c.α = ((CochainComplex.single₀ B).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap c.β ComplexShape.embeddingUpNat)) ≫ Q.e := by
  ext1 q
  apply HomologicalComplex.from_single_hom_ext
  simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    CochainComplex.single₀_map_f_zero] using c.comm_e q

set_option backward.isDefEq.respectTransparency false in
private theorem presentation_base_iso_naturality
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] {P Q : CartanEilenbergPresentation F}
    (c : P.Comparison Q) (q : ℕ) :
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap c.β ComplexShape.embeddingUpNat)) (q : ℤ) ≫
        (presentation_base_iso F Q q).hom =
      (presentation_base_iso F P q).hom ≫ (F.rightDerived q).map c.f := by
  simp only [presentation_base_iso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map, Iso.app_hom]
  rw [← Category.assoc, ← Category.assoc]
  have h := congrArg (fun f ↦ HomologicalComplex.homologyMap f (q : ℤ))
    ((ComplexShape.embeddingUpNat.mapExtendFunctorNatIso F).hom.naturality c.β)
  simp only [HomologicalComplex.homologyMap_comp, Functor.comp_map,
    ComplexShape.Embedding.extendFunctor_map] at h
  rw [h, Category.assoc, Category.assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality_assoc]
  have hn := InjectiveResolution.isoRightDerivedObj_inv_naturality c.f P.J Q.J c.β
    c.comm_ι F q
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at hn
  rw [← hn]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem presentation_homology_resolution_naturality
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] {P Q : CartanEilenbergPresentation F}
    (c : P.Comparison Q) (q : ℕ) :
    (presentation_homology_resolution F P q).ι ≫
        HomologicalComplex.homologyMap c.α (q : ℤ) =
      (CochainComplex.single₀ B).map
        (HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap c.β ComplexShape.embeddingUpNat)) (q : ℤ)) ≫
        (presentation_homology_resolution F Q q).ι := by
  dsimp only [presentation_homology_resolution]
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp,
    presentation_augmentation_naturality F c, HomologicalComplex.homologyMap_comp,
    ← Category.assoc]
  have h := ((CochainComplex.single₀ B).mapHomologicalComplexHomologyIso
    (ComplexShape.up ℤ) (q : ℤ)).inv.naturality
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap c.β ComplexShape.embeddingUpNat))
  simpa only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, Iso.app_inv,
    Category.assoc] using
    congrArg (fun f ↦ f ≫ HomologicalComplex.homologyMap Q.e (q : ℤ)) h.symm

private noncomputable def presentation_iterated_iso
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B] [IsGrothendieckAbelian.{vBT} B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    (P : CartanEilenbergPresentation F) (p q : ℕ) :
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (P.I.homology (q : ℤ))).homology p ≅
      (G.rightDerived p).obj ((F.rightDerived q).obj P.X) :=
  ((presentation_homology_resolution F P q).isoRightDerivedObj G p).symm ≪≫
    (G.rightDerived p).mapIso (presentation_base_iso F P q)

set_option backward.isDefEq.respectTransparency false in
private theorem presentation_iterated_iso_naturality
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B] [IsGrothendieckAbelian.{vBT} B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    {P Q : CartanEilenbergPresentation F} (c : P.Comparison Q) (p q : ℕ) :
    HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (HomologicalComplex.homologyMap c.α (q : ℤ))) p ≫
        (presentation_iterated_iso F G Q p q).hom =
      (presentation_iterated_iso F G P p q).hom ≫
        (F.rightDerived q ⋙ G.rightDerived p).map c.f := by
  let b := HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap c.β ComplexShape.embeddingUpNat)) (q : ℤ)
  have hc := congrArg (fun f ↦ f.f 0)
    (presentation_homology_resolution_naturality F c q)
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at hc
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality b
    (presentation_homology_resolution F P q) (presentation_homology_resolution F Q q)
    (HomologicalComplex.homologyMap c.α (q : ℤ)) hc G p
  change _ = HomologicalComplex.homologyMap _ _ ≫ _ at h
  dsimp only [presentation_iterated_iso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← h, Category.assoc, ← Functor.map_comp]
  rw [presentation_base_iso_naturality F c q, Functor.map_comp]
  simp only [Category.assoc, Functor.comp_map]

set_option backward.isDefEq.respectTransparency false in
private theorem secondFiltration_page_two_iterated_homology
    {C : Type uCT} [Category.{vCT} C] [Abelian C] [IsGrothendieckAbelian.{vCT} C]
    (M : FilteredPageTwoModel C) {ι : Type*}
    (I : ι → HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hzero : ∀ (a : ι) (k : ℤ), k < 0 → IsZero ((I a).X k))
    (L : ∀ a : ι, DecreasingFiltration
      (HomologicalComplex₂.total
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (I a)) (ComplexShape.up ℤ)))
    (hL : ∀ (a : ι) (p n : ℤ), (L a).complexStep p n =
      ((HomologicalComplex₂.secondFiltration
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (I a)) n).step p)) :
    let T := fun a : ι ↦
      (⟨HomologicalComplex₂.total
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (I a)) (ComplexShape.up ℤ), L a⟩ :
          FilteredObject (CochainComplex C ℤ))
    ∃ e : ∀ (a : ι) (p q : ℕ),
        ((M.S.obj (T a)).page 2).X ((p : ℤ), (q : ℤ)) ≅
          ((I a).homology (q : ℤ)).homology p,
      ∀ (a b : ι) (f : I a ⟶ I b) (t : T a ⟶ T b),
        t.hom = HomologicalComplex₂.total.map
          (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f) (ComplexShape.up ℤ) →
        ∀ p q : ℕ,
          ((M.S.map t).hom 2).f ((p : ℤ), (q : ℤ)) ≫ (e b p q).hom =
            (e a p q).hom ≫ HomologicalComplex.homologyMap
              (HomologicalComplex.homologyMap f (q : ℤ)) p := by
  classical
  let T := fun a : ι ↦
    (⟨HomologicalComplex₂.total
      (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I a)) (ComplexShape.up ℤ), L a⟩ :
          FilteredObject (CochainComplex C ℤ))
  obtain ⟨e, he⟩ := secondFiltration_two_column_image I hzero L hL
    (fun a p ↦ M.φ (T a) (p : ℤ) 2 (by omega))
    (fun a p ↦ M.comm_φ (T a) (p : ℤ) 2 (by omega))
  let e' := fun (a : ι) (p q : ℕ) ↦
    M.pageIso (T a) (p : ℤ) (q : ℤ) 2 (by omega) ≪≫ e a p q
  refine ⟨e', ?_⟩
  intro a b f t ht p q
  obtain ⟨s, α, β, hs, hα, hβ, hφ, hn⟩ :=
    M.naturality t (p : ℤ) (q : ℤ) 2 (by omega)
  have hi := he a b f p q (s ((p : ℤ) - 2 + 1)) β
    (by simpa only [← ht] using hs ((p : ℤ) - 2 + 1)) hβ
  apply (cancel_mono ((e b p q).inv ≫
    image.ι (HomologicalComplex.homologyMap (M.φ (T b) (p : ℤ) 2 (by omega))
      ((p : ℤ) + (q : ℤ))))).1
  simp only [e', Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hi]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hn

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_page_two
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B] [IsGrothendieckAbelian.{vBT} B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C] [IsGrothendieckAbelian.{vCT} C]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (M : FilteredPageTwoModel C)
    (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G))
    (hL : ∀ (P : CartanEilenbergPresentation F) (p n : ℤ), (L P).complexStep p n =
      (((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p) :
    let T := fun P : CartanEilenbergPresentation F ↦
      (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ))
    ∃ e : ∀ (P : CartanEilenbergPresentation F) (p q : ℕ),
        ((M.S.obj (T P)).page 2).X ((p : ℤ), (q : ℤ)) ≅
          ((F.rightDerived q ⋙ G.rightDerived p).obj P.X),
      ∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (t : T P ⟶ T Q),
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) →
        ∀ p q : ℕ,
          ((M.S.map t).hom 2).f ((p : ℤ), (q : ℤ)) ≫ (e Q p q).hom =
            (e P p q).hom ≫ (F.rightDerived q ⋙ G.rightDerived p).map c.f := by
  classical
  let H := G.mapHomologicalComplex (ComplexShape.up ℕ)
  let J := fun P : CartanEilenbergPresentation F ↦
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj P.I
  obtain ⟨e, he⟩ := secondFiltration_page_two_iterated_homology M J
    (fun P k hk ↦ H.map_isZero (P.zero_neg k hk)) L hL
  obtain ⟨h, hh⟩ := presentation_horizontal_cohomology F G
  let e' := fun (P : CartanEilenbergPresentation F) (p q : ℕ) ↦
    e P p q ≪≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) p).mapIso
        (h P (q : ℤ)) ≪≫ presentation_iterated_iso F G P p q
  refine ⟨e', ?_⟩
  intro P Q c t ht p q
  have hpage := he P Q ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map c.α) t ht p q
  have hhorizontal := congrArg (fun f ↦ HomologicalComplex.homologyMap f p)
    (hh P Q c (q : ℤ))
  simp only [HomologicalComplex.homologyMap_comp] at hhorizontal
  simp only [e', Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map, Category.assoc]
  rw [reassoc_of% hpage, reassoc_of% hhorizontal,
    presentation_iterated_iso_naturality F G c p q]


private theorem cohomology_image_preserves
    {C : Type uCT} [Category.{vCT} C] [Abelian C]
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (p n : ℤ) :
    ∃ a : ((U.filtration.homologyFiltration n).step p : C) ⟶
        ((V.filtration.homologyFiltration n).step p : C),
      a ≫ ((V.filtration.homologyFiltration n).step p).arrow =
        ((U.filtration.homologyFiltration n).step p).arrow ≫
          HomologicalComplex.homologyMap t.hom n := by
  obtain ⟨s, hs⟩ := t.preserves p
  let a := HomologicalComplex.homologyMap (U.filtration.step p).arrow n
  let b := HomologicalComplex.homologyMap (V.filtration.step p).arrow n
  let u := HomologicalComplex.homologyMap s n
  let v := HomologicalComplex.homologyMap t.hom n
  have huv : u ≫ b = a ≫ v := by
    simp only [u, b, a, v, ← HomologicalComplex.homologyMap_comp, hs]
  let f := image.map (Arrow.homMk' u v huv)
  refine ⟨(imageSubobjectIso a).hom ≫ f ≫ (imageSubobjectIso b).inv, ?_⟩
  change _ ≫ (imageSubobject b).arrow = (imageSubobject a).arrow ≫ v
  simp only [Category.assoc, ← imageSubobject_arrow, Iso.inv_hom_id_assoc]
  have hf : f ≫ image.ι b = image.ι a ≫ v := image.map_ι (Arrow.homMk' u v huv)
  rw [hf]

set_option linter.unusedVariables false in
/-- Comparison maps between the chosen Cartan--Eilenberg presentations are independent
of their lifts from page two. The second-page identifications are natural for the
original map. Identity and composition are preserved. The abutment is identified with
total cohomology, with its image filtration and stabilized pages, naturally for lifts.
Source: Stacks, Tags 015K and 015N
(blueprint: lem-sp-cartan-eilenberg-comparison-independence).

Proof:
1. Use the supplied presentations and construct their second filtrations with lower
   bound zero. Degreewise preservation of the finite sums of diagonal images gives
   filtered total comparison maps.
2. Mathlib's injective-resolution comparison homotopy makes the two underlying lifts
   homotopic. Extend it by zero and apply F. Subtract the CE comparisons and apply the
   double-complex null-homotopy theorem, then restore a homotopy of the comparisons.
   The second steps are split summands of the finite diagonal coproducts, so applying
   G and extension by zero preserves the homotopy and its one-step filtration shift.
3. Filtered homotopy invariance identifies the maps under M.S. Compare arbitrary
   identity and composite lifts with explicit identity and composite comparisons;
   the functor laws of M.S give the required identity and composition equations.
4. The natural two-column cohomology-image calculation, composed with M.pageIso,
   computes the specified second page. Injective horizontal cycles and boundaries
   give the normalized left-exact cohomology comparison. The augmentation supplies
   an explicit injective resolution of horizontal cohomology; isoRightDerivedObj
   and its naturality identify this page with R^p G(R^q F(-)).
5. Take total cohomology with its image filtration as the abutment. Degreewise stable
   quotients and the quotient-image comparison give the stabilized pages. Homotopy
   invariance of cohomology and the induced image maps prove independence,
   functoriality and preservation of the image filtration.
-/
theorem cartanEilenberg_comparison_independence
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B] [IsGrothendieckAbelian.{vBT} B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C] [IsGrothendieckAbelian.{vCT} C]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (M : FilteredPageTwoModel C) :
    ∃ (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G)),
      let T := fun P : CartanEilenbergPresentation F ↦
        (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ))
      (∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
        (L P).complexStep p n =
          ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) ∧
      (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q),
        ∃ t : T P ⟶ T Q,
          t.hom = HomologicalComplex₂.total.map
            ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ)) ∧
      (∀ (P Q : CartanEilenbergPresentation F) (c c' : P.Comparison Q)
        (t t' : T P ⟶ T Q),
        c.f = c'.f →
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) →
        t'.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c'.α) (ComplexShape.up ℤ) →
        M.S.map t = M.S.map t') ∧
      (∀ (P : CartanEilenbergPresentation F) (c : P.Comparison P) (t : T P ⟶ T P),
        c.f = 𝟙 P.X →
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) →
        M.S.map t = 𝟙 (M.S.obj (T P))) ∧
      (∀ (P Q R : CartanEilenbergPresentation F)
        (c : P.Comparison Q) (d : Q.Comparison R) (c' : P.Comparison R)
        (t : T P ⟶ T Q) (u : T Q ⟶ T R) (v : T P ⟶ T R),
        c'.f = c.f ≫ d.f →
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) →
        u.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map d.α) (ComplexShape.up ℤ) →
        v.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c'.α) (ComplexShape.up ℤ) →
        M.S.map v = M.S.map t ≫ M.S.map u) ∧
      (∃ e : ∀ (P : CartanEilenbergPresentation F) (p q : ℕ),
          ((M.S.obj (T P)).page 2).X ((p : ℤ), (q : ℤ)) ≅
            ((F.rightDerived q ⋙ G.rightDerived p).obj P.X),
        ∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q)
          (t : T P ⟶ T Q),
          t.hom = HomologicalComplex₂.total.map
            ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) →
          ∀ p q : ℕ,
            ((M.S.map t).hom 2).f ((p : ℤ), (q : ℤ)) ≫ (e Q p q).hom =
              (e P p q).hom ≫ (F.rightDerived q ⋙ G.rightDerived p).map c.f) ∧
      (∃ (H : CartanEilenbergPresentation F → ℤ → C)
        (h : ∀ (P : CartanEilenbergPresentation F) (n : ℤ), H P n ≅ (P.total G).homology n)
        (HF : ∀ (P : CartanEilenbergPresentation F) (n : ℤ), DecreasingFiltration (H P n))
        (m : ∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (n : ℤ),
          H P n ⟶ H Q n),
        (∀ (P : CartanEilenbergPresentation F) (n : ℤ), (HF P n).IsFinite) ∧
        (∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
          (Subobject.«exists» (h P n).hom).obj ((HF P n).step p) =
            imageSubobject (HomologicalComplex.homologyMap ((L P).step p).arrow n)) ∧
        (∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
          ∃ (R : ℤ) (hR : 2 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
            Nonempty (((M.S.obj (T P)).page r (le_trans hR hr)).X (p, n - p) ≅
              (HF P n).gradedPiece p)) ∧
        (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (n : ℤ),
          m P Q c n ≫ (h Q n).hom = (h P n).hom ≫
            HomologicalComplex.homologyMap
              (HomologicalComplex₂.total.map
                ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ)) n) ∧
        (∀ (P Q : CartanEilenbergPresentation F) (c c' : P.Comparison Q),
          c.f = c'.f → ∀ n : ℤ, m P Q c n = m P Q c' n) ∧
        (∀ (P : CartanEilenbergPresentation F) (c : P.Comparison P),
          c.f = 𝟙 P.X → ∀ n : ℤ, m P P c n = 𝟙 (H P n)) ∧
        (∀ (P Q R : CartanEilenbergPresentation F)
          (c : P.Comparison Q) (d : Q.Comparison R) (e : P.Comparison R),
          e.f = c.f ≫ d.f → ∀ n : ℤ, m P R e n = m P Q c n ≫ m Q R d n) ∧
        (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (p n : ℤ),
          ∃ a : ((HF P n).step p : C) ⟶ ((HF Q n).step p : C),
            a ≫ ((HF Q n).step p).arrow = ((HF P n).step p).arrow ≫ m P Q c n)) := by
  classical
  let J := fun P : CartanEilenbergPresentation F ↦
    (CartanEilenbergPresentation.mappedFunctor G).obj P.I
  have hzero (P : CartanEilenbergPresentation F) (i j : ℤ)
      (h : i < 0 ∨ j < 0) : IsZero (((J P).X i).X j) := by
    rcases h with hi | hj
    · exact (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor C).map_isZero
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map_isZero (P.zero_neg i hi)))
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat j (by
        intro r
        change (r : ℤ) ≠ j
        omega)
  choose L hL htop hbot using fun P ↦ (J P).boundedBelow_secondFiltration 0 (hzero P)
  let T := fun P : CartanEilenbergPresentation F ↦
    (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ))
  have hmap (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) :
      ∃ t : T P ⟶ T Q,
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) :=
    total_secondFiltration_map (J P) (J Q) (L P) (L Q) (hL P) (hL Q)
      ((CartanEilenbergPresentation.mappedFunctor G).map c.α)
  have hfinite (P : CartanEilenbergPresentation F) (n : ℤ) :
      ∃ lo hi : ℤ, (L P).complexStep lo n = ⊤ ∧ (L P).complexStep hi n = ⊥ :=
    ⟨0, n + 1, htop P n, hbot P n⟩
  have homotopies (P Q : CartanEilenbergPresentation F) (c c' : P.Comparison Q)
      (hc : c.f = c'.f) :=
    comparison_filtered_homotopy F G P Q c c' hc (L P) (L Q) (hL P) (hL Q)
  have independent (P Q : CartanEilenbergPresentation F) (c c' : P.Comparison Q)
      (t t' : T P ⟶ T Q) (hc : c.f = c'.f)
      (ht : t.hom = HomologicalComplex₂.total.map
        ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ))
      (ht' : t'.hom = HomologicalComplex₂.total.map
        ((CartanEilenbergPresentation.mappedFunctor G).map c'.α) (ComplexShape.up ℤ)) :
      M.S.map t = M.S.map t' := by
    have hh := homotopies P Q c c' hc
    rw [← ht, ← ht'] at hh
    obtain ⟨H, hH⟩ := hh
    exact (filteredHomotopy_spectralSequence_map_eq (P.total G) (Q.total G)
      (L P) (L Q) (hfinite P) (hfinite Q) t t' H hH).1 M
  refine ⟨L, hL, hmap, independent, ?_, ?_, comparison_page_two F G M L hL, ?_⟩
  · intro P c t hc ht
    have hi : (𝟙 (T P) : T P ⟶ T P).hom = HomologicalComplex₂.total.map
        ((CartanEilenbergPresentation.mappedFunctor G).map (comparison_id P).α)
          (ComplexShape.up ℤ) := by
      simp only [comparison_id, Functor.map_id, HomologicalComplex₂.total.map_id]
      rfl
    exact (independent P P c (comparison_id P) t (𝟙 _) hc ht hi).trans (M.S.map_id _)
  · intro P Q R c d c' t u v hc ht hu hv
    have htu : (t ≫ u).hom = HomologicalComplex₂.total.map
        ((CartanEilenbergPresentation.mappedFunctor G).map (comparison_comp c d).α)
          (ComplexShape.up ℤ) := by
      change t.hom ≫ u.hom = _
      rw [ht, hu]
      simp only [comparison_comp, Functor.map_comp, HomologicalComplex₂.total.map_comp]
    exact (independent P R c' (comparison_comp c d) v (t ≫ u) hc hv htu).trans
      (M.S.map_comp t u)
  · let HF := fun (P : CartanEilenbergPresentation F) (n : ℤ) ↦
      (L P).homologyFiltration n
    let m := fun (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (n : ℤ) ↦
      HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ)) n
    refine ⟨fun P n ↦ (P.total G).homology n, fun _ _ ↦ Iso.refl _, HF, m,
      fun P n ↦ (L P).cohomologyImage_isFinite (hfinite P) n, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro P p n
      simp only [Iso.refl_hom, Subobject.exists_iso_map, Subobject.map_id]
      rfl
    · intro P p n
      obtain ⟨H, hfin, hstep, hstable⟩ := model_convergence M (T P) (hfinite P)
      have heq : H n = HF P n := filtration_ext _ _ (fun p ↦ hstep p n)
      simpa only [heq] using hstable p n
    · intro P Q c n
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · intro P Q c c' hc n
      obtain ⟨H, _⟩ := homotopies P Q c c' hc
      exact H.homologyMap_eq n
    · intro P c hc n
      obtain ⟨H, _⟩ := homotopies P P c (comparison_id P) hc
      change HomologicalComplex.homologyMap _ n = 𝟙 _
      simpa only [comparison_id, Functor.map_id, HomologicalComplex₂.total.map_id,
        HomologicalComplex.homologyMap_id] using H.homologyMap_eq n
    · intro P Q R c d e he n
      obtain ⟨H, _⟩ := homotopies P R e (comparison_comp c d) he
      simpa only [comparison_comp, Functor.map_comp, HomologicalComplex₂.total.map_comp,
        HomologicalComplex.homologyMap_comp] using H.homologyMap_eq n
    · intro P Q c p n
      obtain ⟨t, ht⟩ := hmap P Q c
      simpa only [ht] using cohomology_image_preserves t p n

end CategoryTheory
