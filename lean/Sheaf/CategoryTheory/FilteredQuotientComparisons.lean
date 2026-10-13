/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Algebra.Homology.FilteredComplexQuotientImageComparison
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis
import Sheaf.CategoryTheory.FilteredComplexBoundariesLECycles
import Sheaf.CategoryTheory.FilteredQuotientMapRestrictions

/-!
# Natural comparisons for concrete cycle-boundary quotients

Source: Stacks Project, Homology, Tag 012K, cycle-boundary formulas
(blueprint: lem-sp-filtered-quotient-comparisons).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

private theorem comparison_on_representatives
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (p n r : ℤ) (hr : 1 ≤ r)
    (hBZ : F.complexBoundaries p n r ≤ F.complexCycles p n r)
    (φ : F.complexQuotient p (p + r) (by omega) ⟶
      F.complexQuotient (p - r + 1) (p + 1) (by omega))
    (hφ : F.complexQuotientπ p (p + r) (by omega) ≫ φ =
      Subobject.ofLE (F.step p) (F.step (p - r + 1)) (F.antitone_step (by omega)) ≫
        F.complexQuotientπ (p - r + 1) (p + 1) (by omega)) :
    ∃ e : cokernel (Subobject.ofLE _ _ hBZ) ≅
        image (HomologicalComplex.homologyMap φ n),
      ∃ (z : (F.complexCycleRepresentatives p n r : C) ⟶
          (F.complexCycles p n r : C))
        (g : (F.complexCycleRepresentatives p n r : C) ⟶
          (F.complexQuotient p (p + r) (by omega)).cycles n),
        z ≫ (F.complexCycles p n r).arrow =
          (F.complexCycleRepresentatives p n r).arrow ≫
            (F.complexQuotientπ p (p + 1) (by omega)).f n ∧
        g ≫ (F.complexQuotient p (p + r) (by omega)).iCycles n =
          (F.complexCycleRepresentatives p n r).arrow ≫
            (F.complexQuotientπ p (p + r) (by omega)).f n ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ hBZ) ≫ e.hom ≫
            image.ι (HomologicalComplex.homologyMap φ n) =
          g ≫ (F.complexQuotient p (p + r) (by omega)).homologyπ n ≫
            HomologicalComplex.homologyMap φ n := by
  obtain ⟨ha, hb, ψ, hψ, z, g, hz, hg, e, he⟩ :=
    F.filteredComplex_quotient_image_comparison p n r hr hBZ
  have : Epi (F.complexQuotientπ p (p + r) (by omega)) := by
    dsimp [DecreasingFiltration.complexQuotientπ]
    infer_instance
  have hψφ : ψ = φ := by
    apply (cancel_epi (F.complexQuotientπ p (p + r)
      ((Int.le_add_one le_rfl).trans hb))).1
    exact hψ.trans hφ.symm
  subst ψ
  obtain ⟨z', g', hz'_epi, _, hz', _⟩ :=
    F.filteredComplex_representative_epis p n r (by omega)
  have hzz : z = z' := (cancel_mono (F.complexCycles p n r).arrow).1 (hz.trans hz'.symm)
  subst z'
  exact ⟨e, z, g, hz, hg, hz'_epi, he⟩

private theorem first_page_comparison
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (p n : ℤ)
    (hBZ : F.complexBoundaries p n 1 ≤ F.complexCycles p n 1) :
    ∃ e : cokernel (Subobject.ofLE _ _ hBZ) ≅ (F.gradedPiece p).homology n,
      ∃ (z : (F.complexCycleRepresentatives p n 1 : C) ⟶
          (F.complexCycles p n 1 : C))
        (g : (F.complexCycleRepresentatives p n 1 : C) ⟶
          (F.gradedPiece p).cycles n),
        z ≫ (F.complexCycles p n 1).arrow =
          (F.complexCycleRepresentatives p n 1).arrow ≫
            (F.complexQuotientπ p (p + 1) (by omega)).f n ∧
        g ≫ (F.gradedPiece p).iCycles n =
          (F.complexCycleRepresentatives p n 1).arrow ≫
            (F.complexQuotientπ p (p + 1) (by omega)).f n ∧
        Epi z ∧ z ≫ cokernel.π (Subobject.ofLE _ _ hBZ) ≫ e.hom =
          g ≫ (F.gradedPiece p).homologyπ n := by
  have hcmp := F.filteredComplex_quotient_image_comparison p n 1 le_rfl hBZ
  dsimp only at hcmp
  generalize hx : p - 1 + 1 = a at hcmp
  have hap : a = p := by omega
  clear hx
  subst a
  obtain ⟨ha, hb, φ, hφ, z, g, hz, hg, e, he⟩ := hcmp
  have : Epi (F.complexQuotientπ p (p + 1) (by omega)) := by
    dsimp [DecreasingFiltration.complexQuotientπ]
    infer_instance
  have hφid : φ = 𝟙 (F.complexQuotient p (p + 1) (by omega)) := by
    apply (cancel_epi (F.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl))).1
    simpa only [Subobject.ofLE_refl, Category.id_comp, Category.comp_id] using hφ
  subst φ
  let i := image.eqToIso (HomologicalComplex.homologyMap_id
    (F.complexQuotient p (p + 1) (by omega)) n) ≪≫
      imageMonoIsoSource (𝟙 ((F.gradedPiece p).homology n))
  obtain ⟨z', g', hz'_epi, _, hz', _⟩ :=
    F.filteredComplex_representative_epis p n 1 (by omega)
  have hzz : z = z' := (cancel_mono (F.complexCycles p n 1).arrow).1 (hz.trans hz'.symm)
  subst z'
  refine ⟨e ≪≫ i, z, g, hz, hg, hz'_epi, ?_⟩
  have hi : i.hom = image.ι (HomologicalComplex.homologyMap
      (𝟙 (F.complexQuotient p (p + 1) (by omega))) n) := by
    dsimp only [i, Iso.trans_hom]
    rw [← Category.comp_id ((imageMonoIsoSource _).hom),
      imageMonoIsoSource_hom_self]
    exact (image.eq_fac _).symm
  simpa only [Iso.trans_hom, Category.assoc, hi,
    HomologicalComplex.homologyMap_id, Category.comp_id,
    DecreasingFiltration.gradedPiece, DecreasingFiltration.complexQuotient] using he

private theorem normalized_homology_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ)
    (ZU : Subobject (K.X n)) (ZV : Subobject (L.X n))
    {RU RV QU QV : C} (zU : RU ⟶ (ZU : C)) (zV : RV ⟶ (ZV : C))
    [Epi zU] [Epi zV]
    (gU : RU ⟶ K.cycles n) (gV : RV ⟶ L.cycles n)
    (hzU : zU ≫ ZU.arrow = gU ≫ K.iCycles n)
    (hzV : zV ≫ ZV.arrow = gV ≫ L.iCycles n)
    (πU : (ZU : C) ⟶ QU) (πV : (ZV : C) ⟶ QV) [Epi πU]
    (eU : QU ⟶ K.homology n) (eV : QV ⟶ L.homology n)
    (heU : zU ≫ πU ≫ eU = gU ≫ K.homologyπ n)
    (heV : zV ≫ πV ≫ eV = gV ≫ L.homologyπ n)
    (kz : (ZU : C) ⟶ (ZV : C)) (k : QU ⟶ QV)
    (hkz : kz ≫ ZV.arrow = ZU.arrow ≫ f.f n)
    (hk : πU ≫ k = kz ≫ πV) :
    k ≫ eV = eU ≫ HomologicalComplex.homologyMap f n := by
  have hkerU : kernel.ι zU ≫ gU = 0 := by
    apply (cancel_mono (K.iCycles n)).1
    rw [Category.assoc, ← hzU, ← Category.assoc, kernel.condition, zero_comp, zero_comp]
  have hkerV : kernel.ι zV ≫ gV = 0 := by
    apply (cancel_mono (L.iCycles n)).1
    rw [Category.assoc, ← hzV, ← Category.assoc, kernel.condition, zero_comp, zero_comp]
  let jU := Abelian.epiDesc zU gU hkerU
  let jV := Abelian.epiDesc zV gV hkerV
  have hjU : zU ≫ jU = gU := Abelian.comp_epiDesc _ _ _
  have hjV : zV ≫ jV = gV := Abelian.comp_epiDesc _ _ _
  have hjUi : jU ≫ K.iCycles n = ZU.arrow := by
    apply (cancel_epi zU).1
    simpa only [← Category.assoc, hjU] using hzU.symm
  have hjVi : jV ≫ L.iCycles n = ZV.arrow := by
    apply (cancel_epi zV).1
    simpa only [← Category.assoc, hjV] using hzV.symm
  have hπU : πU ≫ eU = jU ≫ K.homologyπ n := by
    apply (cancel_epi zU).1
    simpa only [← Category.assoc, hjU] using heU
  have hπV : πV ≫ eV = jV ≫ L.homologyπ n := by
    apply (cancel_epi zV).1
    simpa only [← Category.assoc, hjV] using heV
  have hjnat : kz ≫ jV = jU ≫ HomologicalComplex.cyclesMap f n := by
    apply (cancel_mono (L.iCycles n)).1
    rw [Category.assoc, hjVi, Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, hjUi, hkz]
  apply (cancel_epi πU).1
  calc
    πU ≫ k ≫ eV = kz ≫ πV ≫ eV := by rw [← Category.assoc, hk, Category.assoc]
    _ = kz ≫ jV ≫ L.homologyπ n := by rw [hπV]
    _ = jU ≫ HomologicalComplex.cyclesMap f n ≫ L.homologyπ n := by
      rw [← Category.assoc, hjnat, Category.assoc]
    _ = jU ≫ K.homologyπ n ≫ HomologicalComplex.homologyMap f n := by
      rw [← HomologicalComplex.homologyπ_naturality]
    _ = πU ≫ eU ≫ HomologicalComplex.homologyMap f n := by
      rw [← Category.assoc, ← hπU, Category.assoc]

private theorem normalized_image_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {SU SV TU TV : CochainComplex C ℤ} (n : ℤ)
    (a : SU ⟶ SV) (b : TU ⟶ TV) (φU : SU ⟶ TU) (φV : SV ⟶ TV)
    (hw : a ≫ φV = φU ≫ b)
    {RU RV ZU ZV QU QV : C} (ρ : RU ⟶ RV)
    (zU : RU ⟶ ZU) (zV : RV ⟶ ZV) [Epi zU]
    (gU : RU ⟶ SU.cycles n) (gV : RV ⟶ SV.cycles n)
    (πU : ZU ⟶ QU) (πV : ZV ⟶ QV) [Epi πU]
    (eU : QU ⟶ image (HomologicalComplex.homologyMap φU n))
    (eV : QV ⟶ image (HomologicalComplex.homologyMap φV n))
    (heU : zU ≫ πU ≫ eU ≫ image.ι (HomologicalComplex.homologyMap φU n) =
      gU ≫ SU.homologyπ n ≫ HomologicalComplex.homologyMap φU n)
    (heV : zV ≫ πV ≫ eV ≫ image.ι (HomologicalComplex.homologyMap φV n) =
      gV ≫ SV.homologyπ n ≫ HomologicalComplex.homologyMap φV n)
    (kz : ZU ⟶ ZV) (k : QU ⟶ QV)
    (hzρ : zU ≫ kz = ρ ≫ zV)
    (hgρ : gU ≫ HomologicalComplex.cyclesMap a n = ρ ≫ gV)
    (hk : πU ≫ k = kz ≫ πV) :
    k ≫ eV ≫ image.ι (HomologicalComplex.homologyMap φV n) =
      eU ≫ image.ι (HomologicalComplex.homologyMap φU n) ≫
        HomologicalComplex.homologyMap b n := by
  have hH : HomologicalComplex.homologyMap a n ≫ HomologicalComplex.homologyMap φV n =
      HomologicalComplex.homologyMap φU n ≫ HomologicalComplex.homologyMap b n := by
    simp only [← HomologicalComplex.homologyMap_comp, hw]
  apply (cancel_epi πU).1
  apply (cancel_epi zU).1
  calc
    zU ≫ πU ≫ k ≫ eV ≫ image.ι (HomologicalComplex.homologyMap φV n) =
        ρ ≫ zV ≫ πV ≫ eV ≫ image.ι (HomologicalComplex.homologyMap φV n) := by
      rw [← Category.assoc πU, hk]
      simp only [← Category.assoc, hzρ]
    _ = ρ ≫ gV ≫ SV.homologyπ n ≫ HomologicalComplex.homologyMap φV n := by
      rw [heV]
    _ = gU ≫ HomologicalComplex.cyclesMap a n ≫ SV.homologyπ n ≫
        HomologicalComplex.homologyMap φV n := by
      rw [← Category.assoc ρ, ← hgρ]
      simp only [Category.assoc]
    _ = gU ≫ SU.homologyπ n ≫ HomologicalComplex.homologyMap a n ≫
        HomologicalComplex.homologyMap φV n := by
      rw [← HomologicalComplex.homologyπ_naturality_assoc]
    _ = gU ≫ SU.homologyπ n ≫ HomologicalComplex.homologyMap φU n ≫
        HomologicalComplex.homologyMap b n := by rw [hH]
    _ = zU ≫ πU ≫ eU ≫ image.ι (HomologicalComplex.homologyMap φU n) ≫
        HomologicalComplex.homologyMap b n := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ HomologicalComplex.homologyMap b n) heU.symm

private theorem step_restriction_square
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (t : K ⟶ L)
    (s : ∀ i : ℤ, (F.step i : CochainComplex C ℤ) ⟶ (G.step i : CochainComplex C ℤ))
    (hs : ∀ i : ℤ, s i ≫ (G.step i).arrow = (F.step i).arrow ≫ t)
    (a b : ℤ) (h : a ≤ b) :
    Subobject.ofLE (F.step b) (F.step a) (F.antitone_step h) ≫ s a =
      s b ≫ Subobject.ofLE (G.step b) (G.step a) (G.antitone_step h) := by
  apply (cancel_mono (G.step a).arrow).1
  rw [Category.assoc, hs, ← Category.assoc, Subobject.ofLE_arrow,
    Category.assoc, Subobject.ofLE_arrow, hs]

private theorem quotient_descent
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (t : K ⟶ L)
    (s : ∀ i : ℤ, (F.step i : CochainComplex C ℤ) ⟶ (G.step i : CochainComplex C ℤ))
    (hs : ∀ i : ℤ, s i ≫ (G.step i).arrow = (F.step i).arrow ≫ t)
    (a b : ℤ) (h : a ≤ b) :
    ∃ q : F.complexQuotient a b h ⟶ G.complexQuotient a b h,
      F.complexQuotientπ a b h ≫ q = s a ≫ G.complexQuotientπ a b h := by
  let iF := Subobject.ofLE (F.step b) (F.step a) (F.antitone_step h)
  let iG := Subobject.ofLE (G.step b) (G.step a) (G.antitone_step h)
  have hw : iF ≫ s a = s b ≫ iG := step_restriction_square F G t s hs a b h
  refine ⟨cokernel.map iF iG (s b) (s a) hw, ?_⟩
  exact cokernel.π_desc _ _ _

/- Construct quotient comparisons and their naturality without choosing spectral pages.
Source: Stacks Project, Homology, Tag 012K, displayed cycle-boundary formulas
(blueprint: lem-sp-filtered-quotient-comparisons).

Proof: Boundaries are cycles since d squared is zero. Apply the quotient-image
comparison to each filtration and (p,p+q,r). Its quotient morphism equals the
supplied phi: cancel the epic source cokernel projection in their defining squares.
The cycle lift and the projection to Z are uniquely determined by their composites
with the monic cycle inclusions. The latter projection is epic because Z is exactly
the image of representatives in the graded piece; adding F^(p+1) before projecting
has no effect. At r=1 the representatives project to the graded cycles, and the
boundary quotient is their homology. This gives eH and its representative equation.
The comparison eQ is the isomorphism induced by the common kernel of the epic
representative maps to Z/B and to image H(phi). Thus on page one eQ followed by the
image inclusion is eH followed by H(phi).
For a filtered map, choose its uniquely determined step restrictions and descend
through the three cokernels to a,b,g. The differential square sends representatives
to representatives and boundaries to boundaries. Restrict g to Z, obtaining kz,
and descend through B to obtain k, with the displayed two defining equations.
Repeat on page one for kz1,k1. Homology naturality, checked after the epic cycle
representative projection, gives the eH square for any k1 with these equations.
The defining quotient equations and source epimorphism imply phi_U b = a phi_V.
Compose the representative equations with H(b); use that equality and homology
naturality of a to obtain the same representative map on both sides of the eQ
square. Cancel the epic representative projection onto Z/B. This gives eQ
naturality, The representatives used in this check are those of the quotient-image lemma.
All choices are quotients and maps uniquely specified by these squares. -/
set_option linter.unusedVariables false in
/-- Remaining quotient and naturality data after boundary containment.
Source: Stacks Project, Tag 012K.
(blueprint: lem-sp-filtered-quotient-comparisons-rest)

Proof: Apply the quotient-image comparison on each object, identifying its transition
map with φ by cancellation of the source quotient projection. The representative
maps are uniquely specified by their monic inclusion squares; compare them with the
representative-epis theorem to establish Epi z. At page one the transition map is
identity after p-1+1=p, so compose the image comparison with the image-of-identity
isomorphism to get eH and its normalization. Choose the families eH and eQ from
these normalized comparisons: their hom maps are unique because the representative
and cokernel projections are epic and the image inclusions are monic.
Cancel those same projections to prove page-one compatibility of eQ with eH.
For t choose its unique step restrictions from its preservation property and construct
all three quotient maps by cokernel.map. Apply the map-restriction lemma for kz, k,
page-one maps and ρ. Descend the page-one cycle lifts through the epic z to prove
homology naturality for every k₁ satisfying the stipulated squares. The representative
restriction ρ commutes with z and the source cycle lift by cancellation of their monic
inclusions. Cancel the source quotient projection to prove a ≫ φ_V = φ_U ≫ b.
Use the normalized comparison equations, homologyπ naturality and that transition
square to prove image naturality after precomposition with the epic representative
and cokernel projections; cancel them to finish. -/
theorem filteredQuotient_comparisons_rest
    (C : Type u) [Category.{v} C] [Abelian C]
    (φ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
        U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
    (hφ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ φ U p r hr =
          Subobject.ofLE (U.obj.filtration.step p)
            (U.obj.filtration.step (p - r + 1))
            (U.obj.filtration.antitone_step (by omega)) ≫
              U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega))
    (hBZ :  ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r) :
    ∃ eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q),
    ∃ (eQ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
        (p q r : ℤ) (hr : 1 ≤ r),
      cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ≅
        image (HomologicalComplex.homologyMap (φ U p r hr) (p + q))),
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) 1 : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.gradedPiece p).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) 1).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom =
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q)) ∧
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        (eQ U p q 1 (by omega)).hom ≫
            image.ι (HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) =
          (eH U p q).hom ≫
            HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) ∧
      (∀ (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (t : U ⟶ V) (p q r : ℤ) (hr : 1 ≤ r),
        ∃ (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
            (V.obj.filtration.step a : CochainComplex C ℤ))
          (a : U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
            V.obj.filtration.complexQuotient p (p + r) (by omega))
          (b : U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) ⟶
            V.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
          (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p)
          (kz : (U.obj.filtration.complexCycles p (p + q) r : C) ⟶
            (V.obj.filtration.complexCycles p (p + q) r : C))
          (k : cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ⟶
            cokernel (Subobject.ofLE _ _ (hBZ V p q r hr))),
          (∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
            (U.obj.filtration.step i).arrow ≫ t.hom.hom) ∧
          U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ a =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + r) (by omega) ∧
          U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ≫ b =
            s (p - r + 1) ≫
              V.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ∧
          U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
          kz ≫ (V.obj.filtration.complexCycles p (p + q) r).arrow =
            (U.obj.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q) ∧
          cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫ k =
            kz ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q r hr)) ∧
          (∃ (kz₁ : (U.obj.filtration.complexCycles p (p + q) 1 : C) ⟶
              (V.obj.filtration.complexCycles p (p + q) 1 : C))
            (k₁ : cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ⟶
              cokernel (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))),
            kz₁ ≫ (V.obj.filtration.complexCycles p (p + q) 1).arrow =
              (U.obj.filtration.complexCycles p (p + q) 1).arrow ≫ g.f (p + q) ∧
            cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫ k₁ =
              kz₁ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))) ∧
          (∀ k₁ : cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ⟶
              cokernel (Subobject.ofLE _ _ (hBZ V p q 1 (by omega))),
            (∃ kz₁ : (U.obj.filtration.complexCycles p (p + q) 1 : C) ⟶
                (V.obj.filtration.complexCycles p (p + q) 1 : C),
              kz₁ ≫ (V.obj.filtration.complexCycles p (p + q) 1).arrow =
                (U.obj.filtration.complexCycles p (p + q) 1).arrow ≫ g.f (p + q) ∧
              cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫ k₁ =
                kz₁ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))) →
            k₁ ≫ (eH V p q).hom =
              (eH U p q).hom ≫ HomologicalComplex.homologyMap g (p + q)) ∧
          k ≫ (eQ V p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ V p r hr) (p + q)) =
            (eQ U p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ≫
                HomologicalComplex.homologyMap b (p + q)) := by
  classical
  have hH₀ := fun (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ) =>
    first_page_comparison U.obj.filtration p (p + q)
    (hBZ U p q 1 (by omega))
  choose eH hH using hH₀
  have hQ₀ := fun (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r) => comparison_on_representatives U.obj.filtration p (p + q)
    r hr (hBZ U p q r hr) (φ U p r hr) (hφ U p r hr)
  choose eQ hQ using hQ₀
  refine ⟨eH, eQ, hH, ?_, ?_⟩
  · intro U p q
    obtain ⟨z, g, hz, hg, hz_epi, heH⟩ := hH U p q
    obtain ⟨z', g', hz', hg', _, heQ⟩ := hQ U p q 1 (by omega)
    have hzz : z' = z :=
      (cancel_mono (U.obj.filtration.complexCycles p (p + q) 1).arrow).1
        (hz'.trans hz.symm)
    have hgg : g' = g :=
      (cancel_mono ((U.obj.filtration.gradedPiece p).iCycles (p + q))).1
        (hg'.trans hg.symm)
    subst z'
    subst g'
    have := hz_epi
    apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))))).1
    apply (cancel_epi z).1
    have heH' := congrArg (fun f =>
      f ≫ HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) heH
    exact heQ.trans (by
      simpa only [Category.assoc, DecreasingFiltration.gradedPiece,
        DecreasingFiltration.complexQuotient] using heH'.symm)
  · intro U V t p q r hr
    choose s hs using t.hom.preserves
    obtain ⟨a, ha⟩ := quotient_descent U.obj.filtration V.obj.filtration t.hom.hom
      s hs p (p + r) (by omega)
    obtain ⟨b, hb⟩ := quotient_descent U.obj.filtration V.obj.filtration t.hom.hom
      s hs (p - r + 1) (p + 1) (by omega)
    obtain ⟨g, hg⟩ := quotient_descent U.obj.filtration V.obj.filtration t.hom.hom
      s hs p (p + 1) (by omega)
    obtain ⟨kz, k, hkz, hk, hk₁, ρ, hρ⟩ :=
      filteredQuotient_map_restrictions C hBZ U V t p q r hr
        s g hs hg
    refine ⟨s, a, b, g, kz, k, hs, ha, hb, hg, hkz, hk, hk₁, ?_, ?_⟩
    · intro k₁ h₁
      obtain ⟨kz₁, hkz₁, hπ₁⟩ := h₁
      obtain ⟨zU, gU, hzU, hgU, hzU_epi, heU⟩ := hH U p q
      obtain ⟨zV, gV, hzV, hgV, hzV_epi, heV⟩ := hH V p q
      have := hzU_epi
      have := hzV_epi
      exact normalized_homology_naturality g (p + q)
        (U.obj.filtration.complexCycles p (p + q) 1)
        (V.obj.filtration.complexCycles p (p + q) 1) zU zV gU gV
        (hzU.trans hgU.symm) (hzV.trans hgV.symm)
        (cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))))
        (cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega))))
        (eH U p q).hom (eH V p q).hom heU heV kz₁ k₁ hkz₁ hπ₁
    · obtain ⟨zU, gU, hzU, hgU, hzU_epi, heU⟩ := hQ U p q r hr
      obtain ⟨zV, gV, hzV, hgV, _, heV⟩ := hQ V p q r hr
      have := hzU_epi
      have hg_n := congrArg (fun f => f.f (p + q)) hg
      have ha_n := congrArg (fun f => f.f (p + q)) ha
      have hzρ : zU ≫ kz = ρ ≫ zV := by
        apply (cancel_mono (V.obj.filtration.complexCycles p (p + q) r).arrow).1
        rw [Category.assoc, hkz, ← Category.assoc, hzU, Category.assoc]
        rw [show (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ≫
            g.f (p + q) = (s p).f (p + q) ≫
              (V.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) from hg_n]
        rw [← Category.assoc, ← hρ, Category.assoc, ← hzV, ← Category.assoc]
      have hgρ : gU ≫ HomologicalComplex.cyclesMap a (p + q) = ρ ≫ gV := by
        apply (cancel_mono
          ((V.obj.filtration.complexQuotient p (p + r) (by omega)).iCycles (p + q))).1
        rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, hgU,
          Category.assoc]
        rw [show (U.obj.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) ≫
            a.f (p + q) = (s p).f (p + q) ≫
              (V.obj.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) from ha_n]
        rw [← Category.assoc, ← hρ, Category.assoc, ← hgV, ← Category.assoc]
      have hw : a ≫ φ V p r hr = φ U p r hr ≫ b := by
        have : Epi (U.obj.filtration.complexQuotientπ p (p + r) (by omega)) := by
          dsimp [DecreasingFiltration.complexQuotientπ]
          infer_instance
        apply (cancel_epi (U.obj.filtration.complexQuotientπ p (p + r)
          (show p ≤ p + r by omega))).1
        rw [← Category.assoc, ha, Category.assoc, hφ]
        rw [← Category.assoc, ← step_restriction_square U.obj.filtration
          V.obj.filtration t.hom.hom s hs (p - r + 1) p (by omega)]
        rw [Category.assoc, ← hb, ← Category.assoc, ← hφ, Category.assoc]
      exact normalized_image_naturality (p + q) a b (φ U p r hr) (φ V p r hr) hw
        ρ zU zV gU gV
        (cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)))
        (cokernel.π (Subobject.ofLE _ _ (hBZ V p q r hr)))
        (eQ U p q r hr).hom (eQ V p q r hr).hom heU heV kz k hzρ hgρ hk



set_option linter.unusedVariables false in
theorem filteredQuotient_comparisons
    (C : Type u) [Category.{v} C] [Abelian C]
    (φ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
        U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
    (hφ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ φ U p r hr =
          Subobject.ofLE (U.obj.filtration.step p)
            (U.obj.filtration.step (p - r + 1))
            (U.obj.filtration.antitone_step (by omega)) ≫
              U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)) :
    ∃ hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r,
    ∃ eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q),
    ∃ (eQ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
        (p q r : ℤ) (hr : 1 ≤ r),
      cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ≅
        image (HomologicalComplex.homologyMap (φ U p r hr) (p + q))),
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) 1 : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.gradedPiece p).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) 1).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom =
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q)) ∧
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        (eQ U p q 1 (by omega)).hom ≫
            image.ι (HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) =
          (eH U p q).hom ≫
            HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) ∧
      (∀ (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (t : U ⟶ V) (p q r : ℤ) (hr : 1 ≤ r),
        ∃ (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
            (V.obj.filtration.step a : CochainComplex C ℤ))
          (a : U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
            V.obj.filtration.complexQuotient p (p + r) (by omega))
          (b : U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) ⟶
            V.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
          (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p)
          (kz : (U.obj.filtration.complexCycles p (p + q) r : C) ⟶
            (V.obj.filtration.complexCycles p (p + q) r : C))
          (k : cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ⟶
            cokernel (Subobject.ofLE _ _ (hBZ V p q r hr))),
          (∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
            (U.obj.filtration.step i).arrow ≫ t.hom.hom) ∧
          U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ a =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + r) (by omega) ∧
          U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ≫ b =
            s (p - r + 1) ≫
              V.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ∧
          U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
          kz ≫ (V.obj.filtration.complexCycles p (p + q) r).arrow =
            (U.obj.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q) ∧
          cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫ k =
            kz ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q r hr)) ∧
          (∃ (kz₁ : (U.obj.filtration.complexCycles p (p + q) 1 : C) ⟶
              (V.obj.filtration.complexCycles p (p + q) 1 : C))
            (k₁ : cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ⟶
              cokernel (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))),
            kz₁ ≫ (V.obj.filtration.complexCycles p (p + q) 1).arrow =
              (U.obj.filtration.complexCycles p (p + q) 1).arrow ≫ g.f (p + q) ∧
            cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫ k₁ =
              kz₁ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))) ∧
          (∀ k₁ : cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ⟶
              cokernel (Subobject.ofLE _ _ (hBZ V p q 1 (by omega))),
            (∃ kz₁ : (U.obj.filtration.complexCycles p (p + q) 1 : C) ⟶
                (V.obj.filtration.complexCycles p (p + q) 1 : C),
              kz₁ ≫ (V.obj.filtration.complexCycles p (p + q) 1).arrow =
                (U.obj.filtration.complexCycles p (p + q) 1).arrow ≫ g.f (p + q) ∧
              cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫ k₁ =
                kz₁ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))) →
            k₁ ≫ (eH V p q).hom =
              (eH U p q).hom ≫ HomologicalComplex.homologyMap g (p + q)) ∧
          k ≫ (eQ V p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ V p r hr) (p + q)) =
            (eQ U p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ≫
                HomologicalComplex.homologyMap b (p + q)) := by
  let hBZ : ∀ (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r :=
    fun U p q r hr => filteredComplex_boundaries_le_cycles U.obj.obj U.obj.filtration p (p + q) r
  exact ⟨hBZ, filteredQuotient_comparisons_rest C φ hφ hBZ⟩

end CategoryTheory
