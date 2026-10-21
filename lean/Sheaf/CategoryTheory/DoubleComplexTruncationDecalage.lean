/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalageTower
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all WeilConjectures.CategoryTheory.DoubleComplexTotal
import all WeilConjectures.Algebra.Homology.UpperTruncationStepQuotient

/-! # Horizontal smart truncations map into decalage

Source: Stacks Project, Tag 015X, Remark 13.26.15.
(blueprint: lem-sp-double-complex-truncation-decalage).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

open scoped BigOperators

private noncomputable def totalIntProjection
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) (n i j : ℤ) :
    (J.total (.up ℤ)).X n ⟶ (J.X i).X j := by
  classical
  exact J.totalDesc (fun a b _ ↦ if h : a = i ∧ b = j then
    (J.XXIsoOfEq _ _ _ h.1 h.2).hom else 0)

@[reassoc]
private theorem inclusion_totalIntProjection
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (a b n : ℤ) (h : a + b = n) (i j : ℤ) :
    J.ιTotal (.up ℤ) a b n h ≫ totalIntProjection J n i j =
      if h : a = i ∧ b = j then (J.XXIsoOfEq _ _ _ h.1 h.2).hom else 0 := by
  classical
  simp only [totalIntProjection, ι_totalDesc]

@[reassoc (attr := simp)]
private theorem inclusion_totalIntProjection_self
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (a b n : ℤ) (h : a + b = n) :
    J.ιTotal (.up ℤ) a b n h ≫ totalIntProjection J n a b = 𝟙 _ := by
  simp [inclusion_totalIntProjection]

private theorem sum_totalIntProjection_inclusion
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j)) (n : ℤ) :
    ∑ i ∈ Finset.Icc 0 n, totalIntProjection J n i (n - i) ≫
      J.ιTotal (.up ℤ) i (n - i) n (by dsimp [ComplexShape.π]; omega) = 𝟙 _ := by
  classical
  apply total.hom_ext
  intro a b h
  change a + b = n at h
  by_cases hz : a < 0 ∨ b < 0
  · exact (hJ a b hz).eq_of_src _ _
  have ha : a ∈ Finset.Icc 0 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [Preadditive.comp_sum, Finset.sum_eq_single a]
  · have hb : n - a = b := by omega
    subst b
    simp only [inclusion_totalIntProjection_self_assoc, Category.comp_id]
  · intro i hi hia
    rw [inclusion_totalIntProjection_assoc, dif_neg (fun hh ↦ hia hh.1.symm), zero_comp]
  · exact fun hn ↦ (hn ha).elim

private theorem secondFiltration_projection_zero
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (n a i j : ℤ) (hi : n - a < i) :
    ((J.secondFiltration n).step a).arrow ≫ totalIntProjection J n i j = 0 := by
  classical
  apply (Subobject.bot_factors_iff_zero _).1
  apply factors_finset_sup (Finset.Icc a n)
    (fun r ↦ J.ιTotalOrZero (.up ℤ) (n - r) r n) (totalIntProjection J n i j) ⊥
  intro r hr
  have hri : n - r ≠ i := by have := (Finset.mem_Icc.mp hr).1; omega
  rw [J.ιTotalOrZero_eq (.up ℤ) (n - r) r n (by dsimp [ComplexShape.π]; omega),
    inclusion_totalIntProjection, dif_neg (fun h ↦ hri h.1)]
  exact Subobject.factors_zero

private theorem secondFiltration_map_projection_zero
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (n a i j : ℤ) {X : C} (m : X ⟶ (J.total (.up ℤ)).X n) (hi : n - a < i)
    (hm : imageSubobject m ≤ (J.secondFiltration n).step a) :
    m ≫ totalIntProjection J n i j = 0 := by
  let S := (J.secondFiltration n).step a
  have hf : S.Factors m := Subobject.factors_of_le _ hm (by
    simpa only [Category.id_comp] using imageSubobject_factors_comp_self m (𝟙 X))
  rw [← Subobject.factorThru_arrow S m hf, Category.assoc,
    secondFiltration_projection_zero J n a i j hi, comp_zero]

private theorem secondFiltration_boundary_projection
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) (n q : ℤ) :
    ((J.secondFiltration n).step (n - q)).arrow ≫
        (J.total (.up ℤ)).d n (n + 1) ≫ totalIntProjection J (n + 1) (q + 1) (n - q) =
      ((J.secondFiltration n).step (n - q)).arrow ≫
        totalIntProjection J n q (n - q) ≫ (J.d q (q + 1)).f (n - q) := by
  classical
  dsimp only [secondFiltration, DecreasingFiltration.step]
  apply finite_sup_hom_ext (Finset.Icc (n - q) n)
    (fun r ↦ J.ιTotalOrZero (.up ℤ) (n - r) r n)
  intro r hr
  simp only [Category.assoc, Subobject.ofLE_arrow_assoc, imageSubobject_arrow_comp_assoc]
  rw [J.ιTotalOrZero_eq (.up ℤ) (n - r) r n (by dsimp [ComplexShape.π]; omega)]
  rw [← Category.assoc, total_d, Preadditive.comp_add, Preadditive.add_comp,
    ι_D₁, ι_D₂,
    J.d₁_eq (.up ℤ) (show (ComplexShape.up ℤ).Rel (n - r) (n - r + 1) from rfl) r (n + 1)
      (by dsimp [ComplexShape.π]; omega),
    J.d₂_eq (.up ℤ) (n - r) (show (ComplexShape.up ℤ).Rel r (r + 1) from rfl) (n + 1)
      (by dsimp [ComplexShape.π]; omega)]
  have hbound : n - r ≤ q := by have := (Finset.mem_Icc.mp hr).1; omega
  by_cases he : n - r = q
  · subst q
    simp [inclusion_totalIntProjection, inclusion_totalIntProjection_assoc,
      show n - (n - r) = r by omega, show n - r ≠ n - r + 1 by omega,
      ComplexShape.ε₁, XXIsoOfEq]
  · have hne : n - r + 1 ≠ q + 1 := by omega
    have hne' : n - r ≠ q + 1 := by omega
    simp [inclusion_totalIntProjection, inclusion_totalIntProjection_assoc, he, hne, hne']

private theorem truncLE_coordinate_lift
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) (q i j : ℤ)
    {X : C} (f : X ⟶ (J.X i).X j)
    (hi : q < i → f = 0)
    (hq : i = q → f ≫ (J.d i (i + 1)).f j = 0) :
    ∃ g : X ⟶ ((CochainComplex.truncLE J q).X i).X j,
      g ≫ ((CochainComplex.ιTruncLE J q).f i).f j = f := by
  rcases lt_trichotomy i q with h | h | h
  · refine ⟨f ≫ (CochainComplex.truncLEXIso J q i h).inv.f j, ?_⟩
    rw [congrArg (fun z ↦ z.f j)
      ((CochainComplex.truncLE_inclusion_coordinates J q).2 i h)]
    rw [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id]
    exact Category.comp_id f
  · subst i
    let E := HomologicalComplex.eval C (.up ℤ) j
    have hz : E.map (J.iCycles q) ≫ E.map (J.d q (q + 1)) = 0 := by
      rw [← E.map_comp, J.iCycles_d, E.map_zero]
    let hk : IsLimit (KernelFork.ofι (E.map (J.iCycles q)) hz) :=
      isLimitForkMapOfIsLimit' E (J.iCycles_d q (q + 1))
        (J.cyclesIsKernel q (q + 1) (by simp))
    obtain ⟨g, hg⟩ := KernelFork.IsLimit.lift' hk f (hq rfl)
    change X ⟶ (J.cycles q).X j at g
    change g ≫ (J.iCycles q).f j = f at hg
    refine ⟨g ≫ (CochainComplex.truncLEXIsoCycles J q).inv.f j, ?_⟩
    rw [← congrArg (fun z ↦ z.f j)
      (CochainComplex.truncLE_inclusion_coordinates J q).1]
    simp only [HomologicalComplex.comp_f, ← Category.assoc]
    rw [Category.assoc g, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
      HomologicalComplex.id_f, Category.comp_id]
    exact hg
  · refine ⟨0, ?_⟩
    rw [zero_comp, hi h]

private theorem decalage_projection_lift
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (q n i j : ℤ) :
    ∃ g : (L.decalage.step (-q) : CochainComplex C ℤ).X n ⟶
        ((CochainComplex.truncLE J q).X i).X j,
      g ≫ ((CochainComplex.ιTruncLE J q).f i).f j =
        (L.decalage.step (-q)).arrow.f n ≫ totalIntProjection J n i j := by
  let m := (L.decalage.step (-q)).arrow.f n
  have hm : imageSubobject m ≤ (J.secondFiltration n).step (n - q) := by
    change L.decalage.complexStep (-q) n ≤ _
    rw [DecreasingFiltration.decalage_complexStep, hL,
      show -q + n = n - q by omega]
    exact inf_le_left
  apply truncLE_coordinate_lift
  · intro hi
    exact secondFiltration_map_projection_zero J n (n - q) i j m (by omega) hm
  · intro hi
    subst i
    by_cases hnj : n - q = j
    · subst j
      let S := (J.secondFiltration n).step (n - q)
      have hf : S.Factors m := Subobject.factors_of_le _ hm (by
        simpa only [Category.id_comp] using imageSubobject_factors_comp_self m (𝟙 _))
      have hmf : S.factorThru m hf ≫ ((J.secondFiltration n).step (n - q)).arrow = m :=
        Subobject.factorThru_arrow S m hf
      have hb := congrArg (fun z ↦ S.factorThru m hf ≫ z)
        (secondFiltration_boundary_projection J n q)
      simp only [← Category.assoc, hmf] at hb
      dsimp only [m] at hb
      rw [← hb]
      rw [(L.decalage.step (-q)).arrow.comm, Category.assoc]
      have hnext : imageSubobject ((L.decalage.step (-q)).arrow.f (n + 1)) ≤
          (J.secondFiltration (n + 1)).step (n + 1 - q) := by
        change L.decalage.complexStep (-q) (n + 1) ≤ _
        rw [DecreasingFiltration.decalage_complexStep, hL,
          show -q + (n + 1) = n + 1 - q by omega]
        exact inf_le_left
      rw [secondFiltration_map_projection_zero J (n + 1) (n + 1 - q)
        (q + 1) (n - q) _ (by omega) hnext, comp_zero]
    · have hz : totalIntProjection J n q j = 0 := by
        apply total.hom_ext
        intro a b h
        change a + b = n at h
        rw [inclusion_totalIntProjection]
        simp only [comp_zero]
        rw [dif_neg (by rintro ⟨rfl, rfl⟩; omega)]
      rw [hz, comp_zero, zero_comp]

/-- Exactness of coproducts makes a componentwise monic bicomplex map
monic after totalization. -/
private theorem mono_total_map_of_components
    {J J' : HomologicalComplex₂ C (.up ℤ) (.up ℤ)} (f : J ⟶ J')
    (hf : ∀ i j : ℤ, Mono ((f.f i).f j)) : Mono (total.map f (.up ℤ)) := by
  classical
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let D := {ij : ℤ × ℤ // ij.1 + ij.2 = n}
  let X : Discrete D ⥤ C := Discrete.functor (fun ij ↦ (J.X ij.1.1).X ij.1.2)
  let Y : Discrete D ⥤ C := Discrete.functor (fun ij ↦ (J'.X ij.1.1).X ij.1.2)
  let τ : X ⟶ Y := Discrete.natTrans (fun ij ↦ (f.f ij.as.1.1).f ij.as.1.2)
  have : ∀ ij : Discrete D, Mono (τ.app ij) := fun ij ↦ hf _ _
  have : Mono τ := NatTrans.mono_of_mono_app τ
  have hm : Mono (colim.map τ) := inferInstance
  have he : (total.map f (.up ℤ)).f n = colim.map τ := by
    apply total.hom_ext
    intro i j h
    rw [ιTotal_map]
    exact (colimit.ι_map τ ⟨⟨(i, j), h⟩⟩).symm
  rw [he]
  exact hm

/-- The totalized smart truncation lies in the shifted second-filtration steps.
Source: Stacks Project, Tag 015X (blueprint: lem-sp-double-complex-truncation-decalage).

Proof. On a total summand (i,j), with i+j=n, the source vanishes if i>q.
Otherwise j>=n-q. If i<0 or j<0, the target summand is zero. In the remaining
case j<=n, so this summand occurs in the finite supremum defining the second
filtration. Restrict each summand map through that subobject and assemble
using the total coproduct universal property. -/
theorem total_truncLE_secondFiltration
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (q n : ℤ) :
    imageSubobject ((total.map (CochainComplex.ιTruncLE J q) (.up ℤ)).f n) ≤
      (J.secondFiltration n).step (n - q) := by
  classical
  let T : HomologicalComplex₂ C (.up ℤ) (.up ℤ) := CochainComplex.truncLE J q
  let f := CochainComplex.ιTruncLE J q
  let S := (J.secondFiltration n).step (n - q)
  have hf (i j : ℤ) (h : i + j = n) : S.Factors
      ((f.f i).f j ≫ J.ιTotal (.up ℤ) i j n h) := by
    by_cases hi : q < i
    · have hz : IsZero ((T.X i).X j) :=
        (HomologicalComplex.eval C (.up ℤ) j).map_isZero
          (CochainComplex.isZero_of_isStrictlyLE T q i hi)
      rw [hz.eq_of_src ((f.f i).f j) 0, zero_comp]
      exact Subobject.factors_zero
    by_cases hz : i < 0 ∨ j < 0
    · rw [(hJ i j hz).eq_of_tgt ((f.f i).f j) 0, zero_comp]
      exact Subobject.factors_zero
    have hmem : j ∈ Finset.Icc (n - q) n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hs : imageSubobject (J.ιTotal (.up ℤ) i j n h) ≤ S := by
      dsimp only [S, secondFiltration]
      have hh := Finset.le_sup (f := fun r ↦ imageSubobject
        (J.ιTotalOrZero (.up ℤ) (n - r) r n)) hmem
      have he : n - j = i := by omega
      rw [he, J.ιTotalOrZero_eq (.up ℤ) i j n h] at hh
      exact hh
    apply Subobject.factors_of_le _ hs
    exact imageSubobject_factors_comp_self _ _
  let g : (T.total (.up ℤ)).X n ⟶ (S : C) :=
    T.totalDesc (fun i j h ↦ S.factorThru _ (hf i j h))
  have hg : g ≫ S.arrow = (total.map f (.up ℤ)).f n := by
    apply total.hom_ext
    intro i j h
    dsimp [g]
    rw [ι_totalDesc_assoc, Subobject.factorThru_arrow, ιTotal_map]
  exact imageSubobject_le _ g hg

/-- The totalized horizontal upper truncation has its unique restriction to decalage.
Source: Stacks Project, Tag 015X (blueprint: lem-sp-double-complex-truncation-decalage).

Proof. The previous summand calculation puts every degree-n image in L^(n-q).
The universal property of decalage, using the chain-map equation for the second
intersection condition, gives the unique restricted chain map. -/
theorem total_truncLE_decalage_factor
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (q : ℤ) :
    ∃! g : total (CochainComplex.truncLE J q) (.up ℤ) ⟶
        (L.decalage.step (-q) : CochainComplex C ℤ),
      g ≫ (L.decalage.step (-q)).arrow =
        total.map (CochainComplex.ιTruncLE J q) (.up ℤ) := by
  apply (L.decalage_factor_iff _ _).2
  intro n
  rw [hL, show -q + n = n - q by omega]
  exact J.total_truncLE_secondFiltration hJ q n

/-- The specified restriction of a total smart truncation to its decalage step.
Its data is fixed uniquely by the monic inclusion equation proved above. -/
noncomputable def totalTruncLEToDecalage
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (q : ℤ) : total (CochainComplex.truncLE J q) (.up ℤ) ⟶
      (L.decalage.step (-q) : CochainComplex C ℤ) :=
  (J.total_truncLE_decalage_factor hJ L hL q).choose

@[reassoc]
theorem totalTruncLEToDecalage_arrow
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (q : ℤ) :
    J.totalTruncLEToDecalage hJ L hL q ≫ (L.decalage.step (-q)).arrow =
      total.map (CochainComplex.ιTruncLE J q) (.up ℤ) :=
  (J.total_truncLE_decalage_factor hJ L hL q).choose_spec.1

/-- The restriction commutes with any comparison and its specified filtered lift.
Source: Stacks Project, Tag 015X (blueprint: lem-sp-double-complex-truncation-decalage).

Proof. Compose both maps with the monic decalage inclusion. The restriction
formula, the defining equation for the filtered step map, and naturality of
the smart truncation inclusion identify both composites with the same total
comparison. Cancel the inclusion. Thus no arbitrary choice of step maps enters. -/
theorem totalTruncLEToDecalage_naturality
    {J J' : HomologicalComplex₂ C (.up ℤ) (.up ℤ)}
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (hJ' : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J'.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (L' : DecreasingFiltration (J'.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (hL' : ∀ p n : ℤ, L'.complexStep p n = (J'.secondFiltration n).step p)
    (f : J ⟶ J')
    (t : (⟨J.total (.up ℤ), L⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
      (⟨J'.total (.up ℤ), L'⟩ : FilteredObject (CochainComplex C ℤ)))
    (ht : t.hom = total.map f (.up ℤ)) (q : ℤ) :
    total.map (CochainComplex.truncLEMap f q) (.up ℤ) ≫
        J'.totalTruncLEToDecalage hJ' L' hL' q =
      J.totalTruncLEToDecalage hJ L hL q ≫
        DecreasingFiltration.decalageStepMap t (-q) := by
  apply (cancel_mono (L'.decalage.step (-q)).arrow).1
  rw [Category.assoc, totalTruncLEToDecalage_arrow]
  have hs := DecreasingFiltration.decalageStepMap_arrow t (-q)
  rw [Category.assoc, hs, ← Category.assoc, totalTruncLEToDecalage_arrow, ht,
    ← total.map_comp, ← total.map_comp, CochainComplex.ιTruncLE_naturality]

/-- The totalized truncation restriction is monic.
Source: Stacks Project, Tag 015X (blueprint: lem-sp-double-complex-truncation-decalage).

Proof. The smart truncation inclusion is componentwise monic. Exact coproducts
in a Grothendieck category keep its totalization monic. The restriction followed
by the decalage inclusion is that totalization, so the restriction is monic. -/
theorem totalTruncLEToDecalage_mono
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (q : ℤ) : Mono (J.totalTruncLEToDecalage hJ L hL q) := by
  have : Mono (total.map (CochainComplex.ιTruncLE J q) (.up ℤ)) := by
    apply mono_total_map_of_components
    intro i j
    change Mono (((HomologicalComplex.ιTruncLE J
      (ComplexShape.embeddingUpIntLE q)).f i).f j)
    infer_instance
  exact mono_of_mono_fac (J.totalTruncLEToDecalage_arrow hJ L hL q)

/-- Total horizontal smart truncation is exactly the corresponding decalage step.
Source: Stacks Project, Tag 015X (blueprint: lem-sp-double-complex-truncation-decalage).

Proof. Project a decalage element onto each diagonal summand. Components past q
vanish by the first filtration condition. In horizontal degree q the second
condition says that the horizontal differential is zero, so the projection
factors through horizontal cycles. Below q the truncation inclusion is an
isomorphism. Sum these lifts over the finite first-quadrant diagonal. Their
composite with the totalized inclusion is the original decalage inclusion,
by the finite diagonal identity. Monicity of that totalized inclusion forces
the chain-map equation. The two inclusion equations and monicity then prove
that this map is inverse to totalTruncLEToDecalage. -/
theorem totalTruncLEToDecalage_isIso
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (q : ℤ) : IsIso (J.totalTruncLEToDecalage hJ L hL q) := by
  classical
  let T : HomologicalComplex₂ C (.up ℤ) (.up ℤ) := CochainComplex.truncLE J q
  let a := total.map (CochainComplex.ιTruncLE J q) (.up ℤ)
  have ham (n : ℤ) : Mono (a.f n) := by
    have hm : Mono a := by
      apply mono_total_map_of_components
      intro i j
      change Mono (((HomologicalComplex.ιTruncLE J
        (ComplexShape.embeddingUpIntLE q)).f i).f j)
      infer_instance
    change Mono ((HomologicalComplex.eval C (.up ℤ) n).map a)
    infer_instance
  let (n : ℤ) : Mono (a.f n) := ham n
  choose lift hlift using fun n i ↦ decalage_projection_lift J L hL q n i (n - i)
  let g (n : ℤ) : (L.decalage.step (-q) : CochainComplex C ℤ).X n ⟶
      (T.total (.up ℤ)).X n :=
    ∑ i ∈ Finset.Icc 0 n, lift n i ≫
      T.ιTotal (.up ℤ) i (n - i) n (by dsimp [ComplexShape.π]; omega)
  have hg (n : ℤ) : g n ≫ a.f n = (L.decalage.step (-q)).arrow.f n := by
    dsimp only [g, a]
    simp only [Preadditive.sum_comp, Category.assoc, ιTotal_map]
    simp only [← Category.assoc, hlift]
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum, sum_totalIntProjection_inclusion J hJ n,
      Category.comp_id]
  let b : (L.decalage.step (-q) : CochainComplex C ℤ) ⟶ T.total (.up ℤ) :=
    { f := g
      comm' := by
        intro i j hij
        apply (cancel_mono (a.f j)).1
        rw [Category.assoc, ← a.comm, ← Category.assoc, hg, Category.assoc, hg]
        exact (L.decalage.step (-q)).arrow.comm i j }
  have hb : b ≫ a = (L.decalage.step (-q)).arrow := by
    ext n
    exact hg n
  have : Mono a := by
    apply HomologicalComplex.mono_of_mono_f
    exact ham
  refine ⟨⟨b, ?_, ?_⟩⟩
  · apply (cancel_mono a).1
    rw [Category.assoc, hb, totalTruncLEToDecalage_arrow, Category.id_comp]
  · apply (cancel_mono (L.decalage.step (-q)).arrow).1
    rw [Category.assoc, totalTruncLEToDecalage_arrow, hb, Category.id_comp]

end HomologicalComplex₂
