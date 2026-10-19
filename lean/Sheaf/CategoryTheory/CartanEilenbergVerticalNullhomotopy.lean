/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.CategoryTheory.CartanEilenbergExists
public import Mathlib.Algebra.Homology.Homotopy
import Sheaf.CategoryTheory.Abelian.CompatibleNullHomotopyAssembly
import all Sheaf.CategoryTheory.CartanEilenbergComparisonCycleStage
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Vertical null-homotopy of a Cartan--Eilenberg defect

Source: Stacks Project, Tag 015I, compatibility of the boundary/cycle exact sequences;
Weibel, Homological Algebra, Lemma 5.7.10
(blueprint: lem-sp-ce-vertical-nullhomotopy).

We use the bicomplex convention of `exists_cartanEilenberg_resolution`: horizontal
integer degrees and nonnegative vertical degrees. The three row augmentations are
induced by the same bicomplex augmentation. Exactness of these augmented rows is
expressed by quasi-isomorphisms from complexes concentrated in vertical degree zero.
The canonical cycle-column-boundary sequences are short exact in any abelian category.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def columnRow
    {C : Type*} [Category* C] [Abelian C]
    (I : CochainComplex C ℤ) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (I.iCycles p) (factorThruImage (I.d p (p + 1))) (by
    rw [← cancel_mono (image.ι (I.d p (p + 1))), Category.assoc,
      image.fac, HomologicalComplex.iCycles_d, zero_comp])

private theorem columnRow_exact
    {C : Type*} [Category* C] [Abelian C]
    (I : CochainComplex C ℤ) (p : ℤ) : (columnRow I p).ShortExact where
  exact := (columnRow I p).exact_of_f_is_kernel
    (isKernelOfComp (image.ι (I.d p (p + 1))) (I.d p (p + 1))
      (I.cyclesIsKernel p (p + 1) (by simp)) (columnRow I p).zero
      (image.fac (I.d p (p + 1))))
  mono_f := by change Mono (I.iCycles p); infer_instance
  epi_g := by change Epi (factorThruImage (I.d p (p + 1))); infer_instance

private noncomputable def columnRowMap
    {C : Type*} [Category* C] [Abelian C]
    {I J : CochainComplex C ℤ} (e : I ⟶ J) (p : ℤ) :
    columnRow I p ⟶ columnRow J p where
  τ₁ := HomologicalComplex.cyclesMap e p
  τ₂ := e.f p
  τ₃ := image.map (Arrow.homMk' (e.f p) (e.f (p + 1)) (e.comm p (p + 1)))
  comm₁₂ := HomologicalComplex.cyclesMap_i e p
  comm₂₃ := (image.factor_map
    (Arrow.homMk' (e.f p) (e.f (p + 1)) (e.comm p (p + 1)))).symm

private theorem column_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {I J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    (e : I ⟶ J) (p : ℤ) [QuasiIso (HomologicalComplex.cyclesMap e p)]
    [QuasiIso (image.map (Arrow.homMk' (e.f p) (e.f (p + 1)) (e.comm p (p + 1))))] :
    QuasiIso (e.f p) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₂ (columnRowMap e p)
    (columnRow_exact I p) (columnRow_exact J p)
    (by dsimp [columnRowMap]; infer_instance) (by dsimp [columnRowMap]; infer_instance)

private theorem column_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    (J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)) (p : ℤ) (n : ℕ)
    [Injective ((J.cycles p).X n)] [Injective ((image (J.d p (p + 1))).X n)] :
    Injective ((J.X p).X n) := by
  let S := (columnRow J p).map (HomologicalComplex.eval C (ComplexShape.up ℕ) n)
  have hS : S.ShortExact := (columnRow_exact J p).map_of_exact _
  have : Injective S.X₁ := by change Injective ((J.cycles p).X n); infer_instance
  have : Injective S.X₃ := by
    change Injective ((image (J.d p (p + 1))).X n)
    infer_instance
  exact Injective.of_iso hS.splittingOfInjective.isoBinaryBiproduct.symm inferInstance

private theorem single_rows_supported
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (p : ℤ) :
    let S := ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    (∀ n, n ≠ 0 → IsZero ((S.cycles p).X n)) ∧
    (∀ n, n ≠ 0 → IsZero ((image (S.d (p - 1) p)).X n)) ∧
    (∀ n, n ≠ 0 → IsZero ((S.homology p).X n)) := by
  dsimp only
  let S := ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hz (n : ℕ) (hn : n ≠ 0) : IsZero ((S.cycles p).X n) :=
    IsZero.of_mono ((S.iCycles p).f n)
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  exact ⟨hz, fun n hn ↦ IsZero.of_mono ((image.ι (S.d (p - 1) p)).f n)
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn),
    fun n hn ↦ IsZero.of_epi ((S.homologyπ p).f n) (hz n hn)⟩

private theorem supported_nullhomotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    {S X Y : CochainComplex C ℕ}
    (hS : ∀ n : ℕ, n ≠ 0 → IsZero (S.X n))
    (e : S ⟶ X) [QuasiIso e] [∀ n, Injective (Y.X n)]
    (f : X ⟶ Y) (he : e ≫ f = 0) : Nonempty (Homotopy f 0) := by
  let a := supportedIso S hS
  have : QuasiIso (a.hom ≫ e) := by infer_instance
  refine ⟨CochainComplex.homotopyZeroOfQuasiIso (a.hom ≫ e) f ?_⟩
  have h := HomologicalComplex.congr_hom he 0
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    Category.assoc, comp_zero] using congrArg (fun t ↦ a.hom.f 0 ≫ t) h

-- Apply the existing assembly theorem after normalizing the six augmentations.
private theorem supported_assembly
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T X Y : ShortComplex (CochainComplex C ℕ))
    (hS : S.ShortExact) (_hT : T.ShortExact)
    (hX : X.ShortExact) (hY : Y.ShortExact)
    (hS₁ : ∀ n : ℕ, n ≠ 0 → IsZero (S.X₁.X n))
    (hS₂ : ∀ n : ℕ, n ≠ 0 → IsZero (S.X₂.X n))
    (hS₃ : ∀ n : ℕ, n ≠ 0 → IsZero (S.X₃.X n))
    (hT₁ : ∀ n : ℕ, n ≠ 0 → IsZero (T.X₁.X n))
    (hT₂ : ∀ n : ℕ, n ≠ 0 → IsZero (T.X₂.X n))
    (hT₃ : ∀ n : ℕ, n ≠ 0 → IsZero (T.X₃.X n))
    (e : S ⟶ X) (a : T ⟶ Y)
    [QuasiIso e.τ₁] [QuasiIso e.τ₂] [QuasiIso e.τ₃]
    [QuasiIso a.τ₁] [QuasiIso a.τ₂] [QuasiIso a.τ₃]
    [∀ n, Injective (Y.X₁.X n)] [∀ n, Injective (Y.X₂.X n)]
    [∀ n, Injective (Y.X₃.X n)]
    (R : X ⟶ Y) (he : e.τ₂ ≫ R.τ₂ = 0) (s₁ : Homotopy R.τ₁ 0) :
    ∃ (s₂ : Homotopy R.τ₂ 0) (s₃ : Homotopy R.τ₃ 0),
      (∀ n m, X.f.f n ≫ s₂.hom n m = s₁.hom n m ≫ Y.f.f m) ∧
      (∀ n m, s₂.hom n m ≫ Y.g.f m = X.g.f n ≫ s₃.hom n m) := by
  let E := HomologicalComplex.eval C (ComplexShape.up ℕ) 0
  let S₀ := S.map E
  let T₀ := T.map E
  let n₁ := supportedIso S.X₁ hS₁
  let n₂ := supportedIso S.X₂ hS₂
  let n₃ := supportedIso S.X₃ hS₃
  let m₁ := supportedIso T.X₁ hT₁
  let m₂ := supportedIso T.X₂ hT₂
  let m₃ := supportedIso T.X₃ hT₃
  let ε₁ := n₁.hom ≫ e.τ₁
  let ε₂ := n₂.hom ≫ e.τ₂
  let ε₃ := n₃.hom ≫ e.τ₃
  let J₁ : InjectiveResolution T₀.X₁ :=
    { cocomplex := Y.X₁
      ι := m₁.hom ≫ a.τ₁ }
  let J₂ : InjectiveResolution T₀.X₂ :=
    { cocomplex := Y.X₂
      ι := m₂.hom ≫ a.τ₂ }
  let J₃ : InjectiveResolution T₀.X₃ :=
    { cocomplex := Y.X₃
      ι := m₃.hom ≫ a.τ₃ }
  have hεi : ε₁ ≫ X.f = (CochainComplex.single₀ C).map S₀.f ≫ ε₂ := by
    dsimp only [ε₁, ε₂]
    rw [Category.assoc, e.comm₁₂, ← Category.assoc]
    rw [← supportedIso_naturality hS₁ hS₂ S.f, Category.assoc]
    rfl
  have hεπ : ε₂ ≫ X.g = (CochainComplex.single₀ C).map S₀.g ≫ ε₃ := by
    dsimp only [ε₂, ε₃]
    rw [Category.assoc, e.comm₂₃, ← Category.assoc]
    rw [← supportedIso_naturality hS₂ hS₃ S.g, Category.assoc]
    rfl
  have hιj : J₁.ι ≫ Y.f = (CochainComplex.single₀ C).map T₀.f ≫ J₂.ι := by
    change (m₁.hom ≫ a.τ₁) ≫ Y.f = _ ≫ m₂.hom ≫ a.τ₂
    rw [Category.assoc, a.comm₁₂, ← Category.assoc,
      ← supportedIso_naturality hT₁ hT₂ T.f, Category.assoc]
    rfl
  have hιρ : J₂.ι ≫ Y.g = (CochainComplex.single₀ C).map T₀.g ≫ J₃.ι := by
    change (m₂.hom ≫ a.τ₂) ≫ Y.g = _ ≫ m₃.hom ≫ a.τ₃
    rw [Category.assoc, a.comm₂₃, ← Category.assoc,
      ← supportedIso_naturality hT₂ hT₃ T.g, Category.assoc]
    rfl
  obtain ⟨s₂, s₃, _, h₂, h₃⟩ := exists_compatible_nullHomotopies
    S₀ T₀ (hS.map_of_exact E) X.X₁ X.X₂ X.X₃ X.f X.g X.zero
    (fun n ↦ hX.map_of_exact (HomologicalComplex.eval C (ComplexShape.up ℕ) n))
    ε₁ ε₂ ε₃ hεi hεπ J₁ J₂ J₃ Y.f Y.g Y.zero
    (fun n ↦ hY.map_of_exact (HomologicalComplex.eval C (ComplexShape.up ℕ) n))
    hιj hιρ R.τ₁ R.τ₂ R.τ₃ R.comm₁₂.symm R.comm₂₃
    (by dsimp only [ε₂]; rw [Category.assoc, he, comp_zero]) s₁
    (fun m ↦ by rw [s₁.zero 0 m (by simp), comp_zero])
  exact ⟨s₂, s₃, h₂, h₃⟩

private theorem boundary_augmentation_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {S I J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    (e : S ⟶ I) (R : I ⟶ J) (he : e ≫ R = 0) (p : ℤ) :
    (rowHom e p).τ₁ ≫ (rowHom R p).τ₁ = 0 := by
  apply (cancel_mono (image.ι (J.d (p - 1) p))).1
  change (image.map (Arrow.homMk' _ _ (e.comm _ _)) ≫
    image.map (Arrow.homMk' _ _ (R.comm _ _))) ≫ _ = _
  simp only [Category.assoc, image.map_homMk'_ι, zero_comp]
  rw [← Category.assoc, image.map_homMk'_ι, Category.assoc]
  have h := HomologicalComplex.congr_hom he p
  change e.f p ≫ R.f p = 0 at h
  rw [h, comp_zero]

-- One horizontal induction step: boundary → cycle → column → next boundary.
private theorem column_step
    {C : Type u} [Category.{v} C] [Abelian C]
    (K L : CochainComplex C ℤ)
    (I J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (eJ : ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hsource : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (htarget : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p))
    (hinjective : ∀ (p : ℤ) (q : ℕ),
      Injective ((J.cycles p).X q) ∧
      Injective ((image (J.d (p - 1) p)).X q) ∧
      Injective ((J.homology p).X q))
    (R : I ⟶ J) (hR : eI ≫ R = 0) (p : ℤ)
    (b : Homotopy (rowHom R p).τ₁ 0) :
    ∃ (s : Homotopy (R.f p) 0) (b' : Homotopy (columnRowMap R p).τ₃ 0),
      (∀ n m, (image.ι (I.d (p - 1) p)).f n ≫ s.hom n m =
        b.hom n m ≫ (image.ι (J.d (p - 1) p)).f m) ∧
      (∀ n m, s.hom n m ≫ (factorThruImage (J.d p (p + 1))).f m =
        (factorThruImage (I.d p (p + 1))).f n ≫ b'.hom n m) := by
  let S := ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let T := ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have hp : p + 1 - 1 = p := by omega
  have hIout : QuasiIso (columnRowMap eI p).τ₃ := by
    have h := (hsource (p + 1)).2.1
    rw [hp] at h
    exact h
  have hJout : QuasiIso (columnRowMap eJ p).τ₃ := by
    have h := (htarget (p + 1)).2.1
    rw [hp] at h
    exact h
  have : QuasiIso (HomologicalComplex.cyclesMap eI p) := (hsource p).1
  have : QuasiIso (HomologicalComplex.cyclesMap eJ p) := (htarget p).1
  have : QuasiIso (rowHom eI p).τ₁ := (hsource p).2.1
  have : QuasiIso (rowHom eI p).τ₂ := (hsource p).1
  have : QuasiIso (rowHom eI p).τ₃ := (hsource p).2.2
  have : QuasiIso (rowHom eJ p).τ₁ := (htarget p).2.1
  have : QuasiIso (rowHom eJ p).τ₂ := (htarget p).1
  have : QuasiIso (rowHom eJ p).τ₃ := (htarget p).2.2
  have (q : ℕ) : Injective (((row J p).X₁).X q) := (hinjective p q).2.1
  have (q : ℕ) : Injective (((row J p).X₂).X q) := (hinjective p q).1
  have (q : ℕ) : Injective (((row J p).X₃).X q) := (hinjective p q).2.2
  have hzR : (rowHom eI p).τ₂ ≫ (rowHom R p).τ₂ = 0 := by
    dsimp only [rowHom]
    rw [← HomologicalComplex.cyclesMap_comp, hR, HomologicalComplex.cyclesMap_zero]
  obtain ⟨z, _, hz, _⟩ := supported_assembly
    (row S p) (row T p) (row I p) (row J p)
    (row_exact S p) (row_exact T p) (row_exact I p) (row_exact J p)
    (single_rows_supported K p).2.1 (single_rows_supported K p).1
    (single_rows_supported K p).2.2
    (single_rows_supported L p).2.1 (single_rows_supported L p).1
    (single_rows_supported L p).2.2 (rowHom eI p) (rowHom eJ p) (rowHom R p) hzR b
  have hIcol : QuasiIso (columnRowMap eI p).τ₂ := by
    have : QuasiIso (image.map
        (Arrow.homMk' (eI.f p) (eI.f (p + 1)) (eI.comm p (p + 1)))) := hIout
    exact column_quasiIso eI p
  have hJcol : QuasiIso (columnRowMap eJ p).τ₂ := by
    have : QuasiIso (image.map
        (Arrow.homMk' (eJ.f p) (eJ.f (p + 1)) (eJ.comm p (p + 1)))) := hJout
    exact column_quasiIso eJ p
  have : QuasiIso (columnRowMap eI p).τ₁ := (hsource p).1
  have : QuasiIso (columnRowMap eJ p).τ₁ := (htarget p).1
  have (q : ℕ) : Injective (((columnRow J p).X₁).X q) := (hinjective p q).1
  have hOutInj (q : ℕ) : Injective ((image (J.d p (p + 1))).X q) := by
    have h := (hinjective (p + 1) q).2.1
    rw [hp] at h
    exact h
  have (q : ℕ) : Injective (((columnRow J p).X₃).X q) := hOutInj q
  have (q : ℕ) : Injective (((columnRow J p).X₂).X q) := by
    have : Injective ((J.cycles p).X q) := (hinjective p q).1
    have : Injective ((image (J.d p (p + 1))).X q) := hOutInj q
    exact column_injective J p q
  have hSobj (q : ℕ) (hq : q ≠ 0) : IsZero ((S.X p).X q) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hq
  have hTobj (q : ℕ) (hq : q ≠ 0) : IsZero ((T.X p).X q) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hq
  have hSout (q : ℕ) (hq : q ≠ 0) : IsZero ((image (S.d p (p + 1))).X q) :=
    IsZero.of_epi ((factorThruImage (S.d p (p + 1))).f q) (hSobj q hq)
  have hTout (q : ℕ) (hq : q ≠ 0) : IsZero ((image (T.d p (p + 1))).X q) :=
    IsZero.of_epi ((factorThruImage (T.d p (p + 1))).f q) (hTobj q hq)
  have hcolR : (columnRowMap eI p).τ₂ ≫ (columnRowMap R p).τ₂ = 0 := by
    exact HomologicalComplex.congr_hom hR p
  obtain ⟨s, b', hs, hb'⟩ := supported_assembly
    (columnRow S p) (columnRow T p) (columnRow I p) (columnRow J p)
    (columnRow_exact S p) (columnRow_exact T p)
    (columnRow_exact I p) (columnRow_exact J p)
    (single_rows_supported K p).1 hSobj hSout
    (single_rows_supported L p).1 hTobj hTout
    (columnRowMap eI p) (columnRowMap eJ p) (columnRowMap R p) hcolR z
  dsimp only [columnRow, columnRowMap, row, rowHom] at z hz s b' hs hb'
  refine ⟨s, b', ?_, hb'⟩
  intro n m
  have hbi := HomologicalComplex.congr_hom (bi_fac I p) n
  have hbj := HomologicalComplex.congr_hom (bi_fac J p) m
  change (bi I p).f n ≫ (I.iCycles p).f n = _ at hbi
  change (bi J p).f m ≫ (J.iCycles p).f m = _ at hbj
  rw [← hbi, Category.assoc, hs, ← Category.assoc, hz, Category.assoc, hbj]

/-- A bicomplex map zero on its augmentation admits a horizontal-compatible vertical
null-homotopy. Source: Stacks Project, Tag 015I, and Weibel, Homological Algebra,
Lemma 5.7.10 (blueprint: lem-sp-ce-vertical-nullhomotopy).

Proof:
1. The double-complex map R induces maps on boundary, cycle, and horizontal-homology
   rows, all zero on their augmentations. These maps respect both canonical short
   exact sequences B → Z → H and Z → I → B in the abelian category.
2. Apply lem-weil-pbc-acyclic-map-to-injective-nullhomotopy to each exact augmented
   source row and injective target row, adjoining the augmentation in degree -1.
   This gives the three row null-homotopies, zero in vertical degree zero.
3. Induct on horizontal degree p, starting with the zero boundary at p = 0.
   Maintain that the cycle homotopy restricts to the boundary homotopy. Apply
   lem-sp-ce-compatible-homotopy-assembly first to B → Z → H to obtain the cycle
   homotopy extending the prescribed boundary homotopy, then to Z → I → B to obtain
   the column homotopy s and the next boundary homotopy. The source column is exact
   as an extension of exact rows; the target column is injective since the target
   sequence splits degreewise. Both applications respect the augmentations and
   give s = 0 in vertical degree zero. Factor d_h through I → B → Z → I.
   The maintained restriction and quotient identities then give s d_h = d_h s.
   Extend by zero in negative horizontal degrees.

`Homotopy.comm` says R = d_v s + s d_v. Its shape condition gives `s.hom 0 q = 0`
for every natural q, representing the zero component into vertical degree -1.
-/
theorem cartanEilenberg_vertical_nullhomotopy
    (A : Type u) [Category.{v} A] [Abelian A]
    (K L : CochainComplex A ℤ)
    (I J : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
      ⟶ I)
    (eJ : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      ⟶ J)
    (hI : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hJ : ∀ p : ℤ, p < 0 → IsZero (J.X p))
    (hsource : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (htarget : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p))
    (hinjective : ∀ (p : ℤ) (q : ℕ),
      Injective ((J.cycles p).X q) ∧
      Injective ((image (J.d (p - 1) p)).X q) ∧
      Injective ((J.homology p).X q))
    (R : I ⟶ J) (hR : eI ≫ R = 0) :
    (∀ p : ℤ,
      Nonempty (Homotopy (HomologicalComplex.cyclesMap R p) 0) ∧
      Nonempty (Homotopy
        (image.map (Arrow.homMk' (R.f (p - 1)) (R.f p) (R.comm (p - 1) p))) 0) ∧
      Nonempty (Homotopy (HomologicalComplex.homologyMap R p) 0)) ∧
    ∃ s : ∀ p : ℤ, Homotopy (R.f p) 0,
      (∀ (p : ℤ) (q : ℕ), (s p).hom 0 q = 0) ∧
      (∀ (p p' : ℤ) (q q' : ℕ),
        (s p).hom q q' ≫ (J.d p p').f q' =
          (I.d p p').f q ≫ (s p').hom q q') := by
  classical
  have hrows (p : ℤ) :
      Nonempty (Homotopy (HomologicalComplex.cyclesMap R p) 0) ∧
      Nonempty (Homotopy
        (image.map (Arrow.homMk' (R.f (p - 1)) (R.f p) (R.comm (p - 1) p))) 0) ∧
      Nonempty (Homotopy (HomologicalComplex.homologyMap R p) 0) := by
    have : QuasiIso (HomologicalComplex.cyclesMap eI p) := (hsource p).1
    have : QuasiIso (image.map
        (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) :=
      (hsource p).2.1
    have : QuasiIso (HomologicalComplex.homologyMap eI p) := (hsource p).2.2
    have (q : ℕ) : Injective ((J.cycles p).X q) := (hinjective p q).1
    have (q : ℕ) : Injective ((image (J.d (p - 1) p)).X q) := (hinjective p q).2.1
    have (q : ℕ) : Injective ((J.homology p).X q) := (hinjective p q).2.2
    have : QuasiIso (rowHom eI p).τ₁ := (hsource p).2.1
    have (q : ℕ) : Injective ((row J p).X₁.X q) := (hinjective p q).2.1
    refine ⟨?_, ?_, ?_⟩
    · apply supported_nullhomotopy (single_rows_supported K p).1
        (HomologicalComplex.cyclesMap eI p)
      rw [← HomologicalComplex.cyclesMap_comp, hR, HomologicalComplex.cyclesMap_zero]
    · exact supported_nullhomotopy (single_rows_supported K p).2.1
        (rowHom eI p).τ₁ (rowHom R p).τ₁ (boundary_augmentation_zero eI R hR p)
    · apply supported_nullhomotopy (single_rows_supported K p).2.2
        (HomologicalComplex.homologyMap eI p)
      rw [← HomologicalComplex.homologyMap_comp, hR, HomologicalComplex.homologyMap_zero]
  refine ⟨hrows, ?_⟩
  let B (p : ℤ) := Homotopy (rowHom R p).τ₁ 0
  let Incoming (p : ℤ) (b : B p) (s : Homotopy (R.f p) 0) : Prop :=
    ∀ q q', (image.ι (I.d (p - 1) p)).f q ≫ s.hom q q' =
      b.hom q q' ≫ (image.ι (J.d (p - 1) p)).f q'
  have stepInt (p : ℤ) (b : B p) :
      ∃ (s : Homotopy (R.f p) 0) (b' : B (p + 1)),
        Incoming p b s ∧
        (∀ (s' : Homotopy (R.f (p + 1)) 0), Incoming (p + 1) b' s' →
          ∀ q q', s.hom q q' ≫ (J.d p (p + 1)).f q' =
            (I.d p (p + 1)).f q ≫ s'.hom q q') := by
    let P (a : ℤ) : Prop :=
      ∃ (s : Homotopy (R.f p) 0)
        (b' : Homotopy (image.map
          (Arrow.homMk' (R.f a) (R.f (p + 1)) (R.comm a (p + 1)))) 0),
        Incoming p b s ∧
        (∀ (s' : Homotopy (R.f (p + 1)) 0),
          (∀ q q', (image.ι (I.d a (p + 1))).f q ≫ s'.hom q q' =
            b'.hom q q' ≫ (image.ι (J.d a (p + 1))).f q') →
          ∀ q q', s.hom q q' ≫ (J.d p (p + 1)).f q' =
            (I.d p (p + 1)).f q ≫ s'.hom q q')
    change P (p + 1 - 1)
    rw [show p + 1 - 1 = p by omega]
    dsimp only [P]
    obtain ⟨s, b', hs, hb'⟩ :=
      column_step K L I J eI eJ hsource htarget hinjective R hR p b
    dsimp only [columnRowMap, columnRow] at b' hb'
    refine ⟨s, b', hs, ?_⟩
    intro s' hs' q q'
    have hfi := HomologicalComplex.congr_hom (image.fac (I.d p (p + 1))) q
    have hfj := HomologicalComplex.congr_hom (image.fac (J.d p (p + 1))) q'
    change (factorThruImage (I.d p (p + 1))).f q ≫
      (image.ι (I.d p (p + 1))).f q = _ at hfi
    change (factorThruImage (J.d p (p + 1))).f q' ≫
      (image.ι (J.d p (p + 1))).f q' = _ at hfj
    rw [← hfj, ← Category.assoc, hb', Category.assoc, ← hs', ← Category.assoc, hfi]
  have step (n : ℕ) (b : B (n : ℤ)) :
      ∃ (s : Homotopy (R.f (n : ℤ)) 0) (b' : B ((n + 1 : ℕ) : ℤ)),
        Incoming (n : ℤ) b s ∧
        (∀ (s' : Homotopy (R.f ((n + 1 : ℕ) : ℤ)) 0),
          Incoming ((n + 1 : ℕ) : ℤ) b' s' →
            ∀ q q', s.hom q q' ≫ (J.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).f q' =
              (I.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).f q ≫ s'.hom q q') := by
    rw [Nat.cast_add, Nat.cast_one]
    exact stepInt (n : ℤ) b
  choose s next hs hnext using step
  let b : ∀ n : ℕ, B (n : ℤ) := fun n ↦ Nat.rec ((hrows 0).2.1.some) next n
  have hb (n : ℕ) : b (n + 1) = next n (b n) := rfl
  let t (n : ℕ) := s n (b n)
  have ht (n : ℕ) (q q' : ℕ) :
      (t n).hom q q' ≫ (J.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).f q' =
        (I.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).f q ≫ (t (n + 1)).hom q q' := by
    apply hnext n (b n) (t (n + 1))
    rw [← hb n]
    exact hs (n + 1) (b (n + 1))
  let s : ∀ p : ℤ, Homotopy (R.f p) 0 := fun p ↦
    match p with
    | .ofNat n => t n
    | .negSucc n => Homotopy.ofEq ((hI _ (by omega)).eq_of_src _ _)
  have hs_nat (n : ℕ) : s (n : ℤ) = t n := rfl
  refine ⟨s, ?_, ?_⟩
  · intro p q
    exact (s p).zero 0 q (by simp)
  · intro p p' q q'
    by_cases hp : p < 0
    · exact ((HomologicalComplex.eval A (ComplexShape.up ℕ) q).map_isZero (hI p hp)).eq_of_src _ _
    by_cases hp' : p' < 0
    · exact ((HomologicalComplex.eval A (ComplexShape.up ℕ) q').map_isZero
        (hJ p' hp')).eq_of_tgt _ _
    by_cases hrel : (ComplexShape.up ℤ).Rel p p'
    · have hpp' : p' = p + 1 := by simpa only [ComplexShape.up_Rel] using hrel.symm
      subst p'
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ p)
      have hh := ht n q q'
      rw [← hs_nat n, ← hs_nat (n + 1), Nat.cast_add, Nat.cast_one] at hh
      exact hh
    · rw [I.shape _ _ hrel, J.shape _ _ hrel]
      simp

end CategoryTheory
