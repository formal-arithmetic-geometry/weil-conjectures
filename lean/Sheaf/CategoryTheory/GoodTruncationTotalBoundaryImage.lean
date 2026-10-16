/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import all Sheaf.Algebra.Homology.UpperTruncationStepSES

/-! # The degreewise image of the total good-truncation inclusion

Source: Stacks Project, Derived Categories, Tag 015X.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false in
private noncomputable def diagonalProjection
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [M.HasTotal (ComplexShape.up ℤ)] (n p : ℤ) :
    (M.total (ComplexShape.up ℤ)).X n ⟶ (M.X p).X (n - p) :=
  M.totalDesc (fun i j h ↦ if hi : i = p then
    (M.XXIsoOfEq _ _ _ hi (by change i + j = n at h; omega)).hom else 0)

set_option backward.isDefEq.respectTransparency false in
private theorem inclusion_projection
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [M.HasTotal (ComplexShape.up ℤ)] (n p : ℤ) :
    M.ιTotal (ComplexShape.up ℤ) p (n - p) n (by
      change p + (n - p) = n; omega) ≫ diagonalProjection M n p = 𝟙 _ := by
  simp [diagonalProjection, XXIsoOfEq]

set_option backward.isDefEq.respectTransparency false in
private theorem inclusion_projection_ne
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [M.HasTotal (ComplexShape.up ℤ)] (n p i j : ℤ) (h : i + j = n) (hi : i ≠ p) :
    M.ιTotal (ComplexShape.up ℤ) i j n h ≫ diagonalProjection M n p = 0 := by
  simp [diagonalProjection, hi]

set_option backward.isDefEq.respectTransparency false in
private theorem image_sup_hom_ext
    {C : Type u} [Category.{v} C] [Abelian C] {I : Type*} (s : Finset I) {A : I → C}
    {X Y : C} (a : ∀ i, A i ⟶ X)
    (g h : ((s.sup (fun i ↦ imageSubobject (a i)) : Subobject X) : C) ⟶ Y)
    (w : ∀ i, ∀ hi : i ∈ s,
      (factorThruImageSubobject (a i) ≫ Subobject.ofLE _ _
        (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)) ≫ g =
      (factorThruImageSubobject (a i) ≫ Subobject.ofLE _ _
        (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)) ≫ h) :
    g = h := by
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
private theorem factors_image
    {C : Type u} [Category.{v} C] [Abelian C] {X Y : C} (f : X ⟶ Y) (S : Subobject Y)
    (h : imageSubobject f ≤ S) : S.Factors f :=
  (Subobject.imageSubobject_le_iff f S).mp h

set_option backward.isDefEq.respectTransparency false in
private theorem step_inclusion_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [M.HasTotal (ComplexShape.up ℤ)] (n q i j : ℤ) (h : i + j = n)
    (hi : 0 ≤ i) (hiq : i ≤ q) :
    ((M.secondFiltration n).step (n - q)).Factors
      (M.ιTotal (ComplexShape.up ℤ) i j n h) := by
  apply factors_image
  dsimp only [secondFiltration, DecreasingFiltration.step]
  have hj : n - j = i := by omega
  have hh := Finset.le_sup (s := Finset.Icc (n - q) n)
    (f := fun k ↦ imageSubobject
      (M.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n))
    (Finset.mem_Icc.mpr (show n - q ≤ j ∧ j ≤ n by omega))
  rw [hj, M.ιTotalOrZero_eq (ComplexShape.up ℤ) i j n h] at hh
  exact hh

end HomologicalComplex₂
namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in
private theorem truncation_boundary_kernel {D : Type u} [Category.{v} D] [Abelian D]
    (K : CochainComplex D ℤ) (q : ℤ) :
    ∃ h : (K.ιTruncLE q).f q ≫ K.d q (q + 1) = 0,
      Nonempty (IsLimit (KernelFork.ofι ((K.ιTruncLE q).f q) h)) := by
  have h : (K.ιTruncLE q).f q ≫ K.d q (q + 1) = 0 := by
    rw [← CochainComplex.truncLEXIsoCycles_comp_iCycles]
    simp
  exact ⟨h, ⟨IsKernel.isoKernel _ _ (K.cyclesIsKernel q (q + 1) (by simp))
    (K.truncLEXIsoCycles q) (CochainComplex.truncLEXIsoCycles_comp_iCycles K q)⟩⟩

end CochainComplex
namespace HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false in
private theorem boundary_lift
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (q r : ℤ) {A : C} (f : A ⟶ (M.X q).X r)
    (hf : f ≫ (M.d q (q + 1)).f r = 0) :
    ∃ l : A ⟶ ((CochainComplex.truncLE M q).X q).X r,
      l ≫ ((CochainComplex.ιTruncLE M q).f q).f r = f := by
  obtain ⟨hz, ⟨hk⟩⟩ := CochainComplex.truncation_boundary_kernel M q
  let F := HomologicalComplex.eval C (ComplexShape.up ℤ) r
  let h := (KernelFork.ofι ((CochainComplex.ιTruncLE M q).f q) hz).mapIsLimit hk F
  exact ⟨(KernelFork.IsLimit.lift' h f hf).1, (KernelFork.IsLimit.lift' h f hf).2⟩

set_option backward.isDefEq.respectTransparency false in
private theorem total_map_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    {M N : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [M.HasTotal (ComplexShape.up ℤ)] [N.HasTotal (ComplexShape.up ℤ)]
    (f : M ⟶ N) (n : ℤ) (S : Subobject ((N.total (ComplexShape.up ℤ)).X n))
    (hS : ∀ i j : ℤ, ∀ h : i + j = n,
      S.Factors ((f.f i).f j ≫ N.ιTotal (ComplexShape.up ℤ) i j n h)) :
    S.Factors ((total.map f (ComplexShape.up ℤ)).f n) := by
  let l : (M.total (ComplexShape.up ℤ)).X n ⟶ (S : C) :=
    M.totalDesc (fun i j h ↦ S.factorThru _ (hS i j h))
  apply (Subobject.factors_iff _ _).mpr
  refine ⟨l, ?_⟩
  apply total.hom_ext
  intro i j h
  simp [l, ιTotal_map, Subobject.factorThru_arrow]

set_option backward.isDefEq.respectTransparency false in
private theorem cut_total_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hM : ∀ p r : ℤ, p < 0 ∨ r < 0 → IsZero ((M.X p).X r)) (q n : ℤ) :
    ((M.secondFiltration n).step (n - q)).Factors
      ((total.map (CochainComplex.ιTruncLE M q) (ComplexShape.up ℤ)).f n) := by
  apply total_map_factors
  intro i j h
  by_cases hi : i < 0
  · rw [(hM i j (Or.inl hi)).eq_zero_of_tgt
      (((CochainComplex.ιTruncLE M q).f i).f j), zero_comp]
    exact Subobject.factors_zero
  by_cases hiq : i ≤ q
  · exact Subobject.factors_of_factors_right
      (((CochainComplex.ιTruncLE M q).f i).f j)
      (step_inclusion_factors M n q i j h (by omega) hiq)
  · have hz := CochainComplex.isZero_of_isStrictlyLE (CochainComplex.truncLE M q)
      q i (by omega)
    have hz' := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero hz
    rw [hz'.eq_zero_of_src (((CochainComplex.ιTruncLE M q).f i).f j), zero_comp]
    exact Subobject.factors_zero

set_option backward.isDefEq.respectTransparency false in
private theorem step_arrow_ext
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [M.HasTotal (ComplexShape.up ℤ)] (n q : ℤ) {Y : C}
    (f g : (M.total (ComplexShape.up ℤ)).X n ⟶ Y)
    (h : ∀ i j : ℤ, ∀ hij : i + j = n, 0 ≤ i → i ≤ q →
      M.ιTotal (ComplexShape.up ℤ) i j n hij ≫ f =
        M.ιTotal (ComplexShape.up ℤ) i j n hij ≫ g) :
    ((M.secondFiltration n).step (n - q)).arrow ≫ f =
      ((M.secondFiltration n).step (n - q)).arrow ≫ g := by
  dsimp only [secondFiltration, DecreasingFiltration.step]
  apply image_sup_hom_ext (Finset.Icc (n - q) n)
    (fun k ↦ M.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n)
  intro k hk
  simp only [Category.assoc, Subobject.ofLE_arrow_assoc, imageSubobject_arrow_comp_assoc]
  rw [M.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - k) k n (by
    change (n - k) + k = n; omega)]
  exact h (n - k) k (by omega) (by have := Finset.mem_Icc.mp hk; omega)
    (by have := Finset.mem_Icc.mp hk; omega)

set_option backward.isDefEq.respectTransparency false in
private theorem step_projection_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [M.HasTotal (ComplexShape.up ℤ)] (n q p : ℤ) (hp : q < p) :
    ((M.secondFiltration n).step (n - q)).arrow ≫ diagonalProjection M n p = 0 := by
  have hh := step_arrow_ext M n q (diagonalProjection M n p) 0 (by
    intro i j h hi hiq
    rw [comp_zero, inclusion_projection_ne M n p i j h (by omega)])
  simpa only [comp_zero] using hh

set_option backward.isDefEq.respectTransparency false in
private theorem step_reconstruction
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [M.HasTotal (ComplexShape.up ℤ)] (n q : ℤ) :
    ((M.secondFiltration n).step (n - q)).arrow ≫
        (∑ p ∈ Finset.Icc (0 : ℤ) q, diagonalProjection M n p ≫
          M.ιTotal (ComplexShape.up ℤ) p (n - p) n (by
            change p + (n - p) = n; omega)) =
      ((M.secondFiltration n).step (n - q)).arrow := by
  conv_rhs => rw [← Category.comp_id ((M.secondFiltration n).step (n - q)).arrow]
  apply step_arrow_ext M n q
  intro i j hij hi hiq
  have hj : j = n - i := by omega
  subst j
  simp only [Category.comp_id, Preadditive.comp_sum, ← Category.assoc]
  rw [Finset.sum_eq_single i]
  · rw [inclusion_projection, Category.id_comp]
  · intro b hb hbi
    rw [inclusion_projection_ne M n b i (n - i) hij (Ne.symm hbi), zero_comp]
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨hi, hiq⟩)).elim

set_option backward.isDefEq.respectTransparency false in
private theorem step_boundary_differential
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [M.HasTotal (ComplexShape.up ℤ)] (n q : ℤ) :
    ((M.secondFiltration n).step (n - q)).arrow ≫
        (M.total (ComplexShape.up ℤ)).d n (n + 1) ≫
          diagonalProjection M (n + 1) (q + 1) =
      ((M.secondFiltration n).step (n - q)).arrow ≫ diagonalProjection M n q ≫
        (M.d q (q + 1)).f (n - q) ≫
          (M.XXIsoOfEq _ _ _ rfl (by omega : n - q = n + 1 - (q + 1))).hom := by
  apply step_arrow_ext M n q
  intro i j hij hi hiq
  rw [← Category.assoc, total_d, Preadditive.comp_add, ι_D₁, ι_D₂,
    Preadditive.add_comp]
  rw [M.d₁_eq' (ComplexShape.up ℤ)
      (show (ComplexShape.up ℤ).Rel i (i + 1) by rfl),
    M.d₂_eq' (ComplexShape.up ℤ) i
      (show (ComplexShape.up ℤ).Rel j (j + 1) by rfl)]
  have hι₁ := M.ιTotalOrZero_eq (ComplexShape.up ℤ) (i + 1) j (n + 1)
    (by change (i + 1) + j = n + 1; omega)
  have hι₂ := M.ιTotalOrZero_eq (ComplexShape.up ℤ) i (j + 1) (n + 1)
    (by change i + (j + 1) = n + 1; omega)
  rw [hι₁, hι₂]
  change ((1 : ℤˣ) • _) ≫ _ + (i.negOnePow • _) ≫ _ = _
  simp only [one_smul, Category.assoc, CategoryTheory.Linear.units_smul_comp,
    inclusion_projection_ne M (n + 1) (q + 1) i (j + 1)
      (by omega) (by omega), comp_zero, smul_zero, add_zero]
  by_cases hiq' : i = q
  · subst i
    have hj : j = n - q := by omega
    subst j
    simp [diagonalProjection, XXIsoOfEq]
  · rw [inclusion_projection_ne M (n + 1) (q + 1) (i + 1) j
        (by omega) (by omega), comp_zero,
      ← Category.assoc (M.ιTotal (ComplexShape.up ℤ) i j n hij),
      inclusion_projection_ne M n q i j hij hiq', zero_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem cut_total_lift
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (q n : ℤ) {A : C} (f : A ⟶ (M.total (ComplexShape.up ℤ)).X n)
    (hf : ((M.secondFiltration n).step (n - q)).Factors f)
    (hd : ((M.secondFiltration (n + 1)).step (n + 1 - q)).Factors
      (f ≫ (M.total (ComplexShape.up ℤ)).d n (n + 1))) :
    ∃ l : A ⟶ (HomologicalComplex₂.total (CochainComplex.truncLE M q) (ComplexShape.up ℤ)).X n,
      l ≫ (total.map (CochainComplex.ιTruncLE M q) (ComplexShape.up ℤ)).f n = f := by
  classical
  let S := (M.secondFiltration n).step (n - q)
  let Q := (M.secondFiltration (n + 1)).step (n + 1 - q)
  let d := (M.total (ComplexShape.up ℤ)).d n (n + 1)
  have hz : f ≫ d ≫ diagonalProjection M (n + 1) (q + 1) = 0 := by
    calc
      _ = Q.factorThru (f ≫ d) hd ≫ Q.arrow ≫
          diagonalProjection M (n + 1) (q + 1) := by
        simp only [← Category.assoc, Subobject.factorThru_arrow]
      _ = 0 := by rw [step_projection_zero M (n + 1) q (q + 1) (by omega), comp_zero]
  have hw := congrArg (fun t ↦ S.factorThru f hf ≫ t)
    (step_boundary_differential M n q)
  dsimp only [S] at hw
  simp only [← Category.assoc, Subobject.factorThru_arrow] at hw
  simp only [Category.assoc] at hw
  have hb : f ≫ diagonalProjection M n q ≫ (M.d q (q + 1)).f (n - q) = 0 := by
    apply (cancel_mono (M.XXIsoOfEq _ _ _ rfl
      (by omega : n - q = n + 1 - (q + 1))).hom).1
    simpa only [zero_comp, Category.assoc] using hw.symm.trans hz
  obtain ⟨b, hb⟩ := boundary_lift M q (n - q) (f ≫ diagonalProjection M n q)
    (by simpa only [Category.assoc] using hb)
  let K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    CochainComplex.truncLE M q
  let ι := CochainComplex.ιTruncLE M q
  have hiso (p : ℤ) (hp : p < q) : IsIso ((ι.f p).f (n - p)) := by
    have : IsIso (ι.f p) := CochainComplex.isIso_ιTruncLE_f M q p hp
    infer_instance
  let a (p : ℤ) : A ⟶ (K.X p).X (n - p) :=
    if hp : p < q then
      letI := hiso p hp
      f ≫ diagonalProjection M n p ≫ inv ((ι.f p).f (n - p))
    else if hpq : p = q then
      b ≫ (K.XXIsoOfEq _ _ _ hpq.symm (by omega : n - q = n - p)).hom
    else 0
  have ha (p : ℤ) (hp : p ≤ q) :
      a p ≫ ((ι.f p).f (n - p)) = f ≫ diagonalProjection M n p := by
    dsimp only [a]
    split_ifs with hlt heq
    · have := hiso p hlt
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · subst p
      dsimp only [K, ι]
      simpa [XXIsoOfEq] using hb
    · omega
  let l : A ⟶ (K.total (ComplexShape.up ℤ)).X n :=
    ∑ p ∈ Finset.Icc (0 : ℤ) q, a p ≫ K.ιTotal (ComplexShape.up ℤ) p (n - p) n (by
      change p + (n - p) = n; omega)
  refine ⟨l, ?_⟩
  calc
    _ = ∑ p ∈ Finset.Icc (0 : ℤ) q, f ≫ diagonalProjection M n p ≫
        M.ιTotal (ComplexShape.up ℤ) p (n - p) n (by
          change p + (n - p) = n; omega) := by
      dsimp only [l]
      rw [Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Category.assoc, ιTotal_map, ← Category.assoc, ha p (Finset.mem_Icc.mp hp).2,
        Category.assoc]
    _ = f ≫ ∑ p ∈ Finset.Icc (0 : ℤ) q, diagonalProjection M n p ≫
        M.ιTotal (ComplexShape.up ℤ) p (n - p) n (by
          change p + (n - p) = n; omega) := by rw [Preadditive.comp_sum]
    _ = f := by
      conv_lhs => rw [← Subobject.factorThru_arrow S f hf]
      rw [Category.assoc, step_reconstruction, Subobject.factorThru_arrow]

set_option backward.isDefEq.respectTransparency false in
/-- The boundary kernel gives the image of the good-cut total on a nonempty cut diagonal.
Source: Stacks Project, Derived Categories, Tag 015X, second filtration.
(blueprint: lem-sp-good-truncation-total-boundary-image).

Proof. In degree n the total is the finite direct sum of M^(p,n-p), 0<=p<=n.
The second filtration at n-q is its direct sum over p<=q. Inside it, the inverse
image of the next vertical step under the total differential is the kernel of
its composite with projection onto the remaining boundary summand at p=q+1.
All vertical differentials and horizontal differentials from p<q already land
in that next step. Thus this kernel retains the full terms with p<q and replaces
the boundary p=q term by its horizontal kernel. Evaluating the horizontal good
truncation gives exactly these terms. The finite direct-sum inclusions and kernel
lifts show both containments of the displayed subobjects. Terms with p>q in the
cut vanish, while omitted negative-index terms vanish by hM. The assumptions
0<=q<=n ensure that the boundary summand has a nonnegative
vertical index. At q=0 there are no retained strict columns, so the same kernel
calculation applies without a preceding direct-sum summand. -/
theorem good_truncation_total_boundary_image
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hM : ∀ p r : ℤ, p < 0 ∨ r < 0 → IsZero ((M.X p).X r))
    (q : ℤ) (hq : 0 ≤ q) (n : ℤ) (hqn : q ≤ n) :
    imageSubobject ((total.map (CochainComplex.ιTruncLE M q)
      (ComplexShape.up ℤ)).f n) =
      (M.secondFiltration n).step (n - q) ⊓
        (Subobject.pullback ((M.total (ComplexShape.up ℤ)).d n (n + 1))).obj
          ((M.secondFiltration (n + 1)).step (n - q + 1)) := by
  have _ := hq
  have _ := hqn
  let ι := total.map (CochainComplex.ιTruncLE M q) (ComplexShape.up ℤ)
  let S := (M.secondFiltration n).step (n - q)
  let Q := (M.secondFiltration (n + 1)).step (n - q + 1)
  let d := (M.total (ComplexShape.up ℤ)).d n (n + 1)
  change imageSubobject (ι.f n) = S ⊓ (Subobject.pullback d).obj Q
  apply le_antisymm
  · apply le_inf
    · exact (Subobject.imageSubobject_le_iff _ _).mpr (cut_total_factors M hM q n)
    · apply (Subobject.imageSubobject_le_iff _ _).mpr
      apply pullback_factors
      rw [ι.comm n (n + 1)]
      apply Subobject.factors_of_factors_right
      have he : n - q + 1 = n + 1 - q := by omega
      simpa only [Q, he] using cut_total_factors M hM q (n + 1)
  · let R := S ⊓ (Subobject.pullback d).obj Q
    have hf : S.Factors R.arrow := Subobject.inf_arrow_factors_left _ _
    have hd : Q.Factors (R.arrow ≫ d) :=
      (pullback_factors_iff d Q R.arrow).mp (Subobject.inf_arrow_factors_right _ _)
    have he : n - q + 1 = n + 1 - q := by omega
    obtain ⟨l, hl⟩ := cut_total_lift M q n R.arrow hf (by
      simpa only [Q, he] using hd)
    change R ≤ imageSubobject (ι.f n)
    calc
      R = imageSubobject R.arrow := by rw [imageSubobject_mono, Subobject.mk_arrow]
      _ = imageSubobject (l ≫ ι.f n) := by
        change l ≫ ι.f n = R.arrow at hl
        rw [hl]
      _ ≤ imageSubobject (ι.f n) := imageSubobject_comp_le _ _

end HomologicalComplex₂
