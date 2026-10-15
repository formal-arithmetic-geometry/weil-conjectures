/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution

/-!
# Assembly of compatible null-homotopies

Source: Stacks Project, Derived Categories, Tag 015I, boundary/cycle exact sequences;
Weibel, Homological Algebra, Lemma 5.7.10
(blueprint: lem-sp-ce-compatible-homotopy-assembly).
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory

private theorem nullHomotopicMap_of_homotopy
    {C : Type u} [Category.{v} C] [Preadditive C]
    {K L : CochainComplex C ℕ} {R : K ⟶ L} (s : Homotopy R 0) :
    Homotopy.nullHomotopicMap s.hom = R := by
  ext n
  simpa only [Homotopy.nullHomotopicMap, HomologicalComplex.zero_f, add_zero] using
    (s.comm n).symm

-- Preserve the augmentation interface; some of its hypotheses are redundant in this proof.
set_option linter.unusedVariables false in
/-- A prescribed null-homotopy on the subcomplex extends to compatible null-homotopies
on the middle complex and quotient. Source: Stacks Project, Tag 015I, boundary/cycle
exact sequences; Weibel, Homological Algebra, Lemma 5.7.10
(blueprint: lem-sp-ce-compatible-homotopy-assembly).

The source augmentations are quasi-isomorphisms from `single₀`, expressing exactness
of the augmented complexes. The target resolutions may resolve different objects:
`S` is the source augmentation sequence and `T` the target augmentation sequence.
The complexes are indexed from zero, as in the node's proof. A homotopy's components
out of degree zero are all zero; this encodes the absent degree minus one term.

Proof, step 1: extend each component of `sZ` across the monomorphism `i` by
injectivity of `JZ`. Injectivity also splits `j`, giving a section of `ρ`.
Apply `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` to the augmented exact
complex `B` and its augmentation-zero map `RB`, obtaining a null-homotopy `sB`.
Step 2: combine the extended `sZ` and the lift of `sB` to a graded map `t` with
`t i = j sZ` and `ρ t = sB π`. The defect `RI - (d t + t d)` vanishes on `i` and
under `ρ`, so exactness factors it as `j E' π`. The induced chain map `E'` from
`B` to `JZ` vanishes on the augmentation, using that `t` vanishes in degree zero
and that the augmentation quotient map is epic.
Step 3: the same acyclic-to-injective lemma gives a null-homotopy `k` of `E'`.
Set `sI = t + j k π`. This kills the defect and preserves both compatibility
identities since `π i = 0` and `ρ j = 0`.
Step 4: all constructed homotopies vanish in degree zero, giving the stated
normalization and all four identities. -/
theorem exists_compatible_nullHomotopies
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact)
    (Z I B : CochainComplex C ℕ)
    (i : Z ⟶ I) (π : I ⟶ B) (hiπ : i ≫ π = 0)
    (hsource : ∀ n : ℕ, ((ShortComplex.mk i π hiπ).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (εZ : (CochainComplex.single₀ C).obj S.X₁ ⟶ Z)
    (εI : (CochainComplex.single₀ C).obj S.X₂ ⟶ I)
    (εB : (CochainComplex.single₀ C).obj S.X₃ ⟶ B)
    [QuasiIso εZ] [QuasiIso εI] [QuasiIso εB]
    (hεi : εZ ≫ i = (CochainComplex.single₀ C).map S.f ≫ εI)
    (hεπ : εI ≫ π = (CochainComplex.single₀ C).map S.g ≫ εB)
    (JZ : InjectiveResolution T.X₁) (JI : InjectiveResolution T.X₂)
    (JB : InjectiveResolution T.X₃)
    (j : JZ.cocomplex ⟶ JI.cocomplex) (ρ : JI.cocomplex ⟶ JB.cocomplex)
    (hjρ : j ≫ ρ = 0)
    (htarget : ∀ n : ℕ, ((ShortComplex.mk j ρ hjρ).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (hιj : JZ.ι ≫ j = (CochainComplex.single₀ C).map T.f ≫ JI.ι)
    (hιρ : JI.ι ≫ ρ = (CochainComplex.single₀ C).map T.g ≫ JB.ι)
    (RZ : Z ⟶ JZ.cocomplex) (RI : I ⟶ JI.cocomplex) (RB : B ⟶ JB.cocomplex)
    (hRi : i ≫ RI = RZ ≫ j) (hRπ : RI ≫ ρ = π ≫ RB)
    (hRε : εI ≫ RI = 0) (sZ : Homotopy RZ 0)
    (hsZε : ∀ m : ℕ, εZ.f 0 ≫ sZ.hom 0 m = 0) :
    ∃ (sI : Homotopy RI 0) (sB : Homotopy RB 0),
      (∀ m : ℕ, sI.hom 0 m = 0 ∧ sB.hom 0 m = 0) ∧
      (∀ n m : ℕ, i.f n ≫ sI.hom n m = sZ.hom n m ≫ j.f m) ∧
      (∀ n m : ℕ, sI.hom n m ≫ ρ.f m = π.f n ≫ sB.hom n m) := by
  classical
  -- The quotient map is zero on its augmentation, so the resolution comparison applies.
  have hεπ₀ : εI.f 0 ≫ π.f 0 = S.g ≫ εB.f 0 := by
    simpa using HomologicalComplex.congr_hom hεπ 0
  have hRπ₀ : RI.f 0 ≫ ρ.f 0 = π.f 0 ≫ RB.f 0 := by
    simpa using HomologicalComplex.congr_hom hRπ 0
  have hRε₀ : εI.f 0 ≫ RI.f 0 = 0 := by
    simpa using HomologicalComplex.congr_hom hRε 0
  have hB : εB.f 0 ≫ RB.f 0 = 0 := by
    have := hS.epi_g
    rw [← cancel_epi S.g, ← Category.assoc, ← hεπ₀, Category.assoc,
      ← hRπ₀, ← Category.assoc, hRε₀, Limits.zero_comp, Limits.comp_zero]
  let sB : Homotopy RB 0 := CochainComplex.homotopyZeroOfQuasiIso εB RB hB
  -- Extend the prescribed homotopy and lift the quotient homotopy degreewise.
  have hmono (n : ℕ) : Mono (i.f n) := (hsource n).mono_f
  let a (n m : ℕ) : I.X n ⟶ JZ.cocomplex.X m := by
    have := hmono n
    exact if (ComplexShape.up ℕ).Rel m n then
      Injective.factorThru (sZ.hom n m) (i.f n)
    else 0
  have ha (n m : ℕ) : i.f n ≫ a n m = sZ.hom n m := by
    have := hmono n
    dsimp [a]
    split_ifs with h
    · exact Injective.comp_factorThru _ _
    · rw [Limits.comp_zero, sZ.zero n m h]
  let split (m : ℕ) : ((ShortComplex.mk j ρ hjρ).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) m)).Splitting := by
    have : Injective (((ShortComplex.mk j ρ hjρ).map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) m)).X₁) := JZ.injective m
    exact (htarget m).splittingOfInjective
  let Q (m : ℕ) : JB.cocomplex.X m ⟶ JI.cocomplex.X m := (split m).s
  have hQ (m : ℕ) : Q m ≫ ρ.f m = 𝟙 _ := (split m).s_g
  have hiπf (n : ℕ) : i.f n ≫ π.f n = 0 := by
    simpa using HomologicalComplex.congr_hom hiπ n
  have hjρf (m : ℕ) : j.f m ≫ ρ.f m = 0 := by
    simpa using HomologicalComplex.congr_hom hjρ m
  let t (n m : ℕ) : I.X n ⟶ JI.cocomplex.X m :=
    a n m ≫ j.f m + π.f n ≫ sB.hom n m ≫ Q m
  have hti (n m : ℕ) : i.f n ≫ t n m = sZ.hom n m ≫ j.f m := by
    dsimp [t]
    rw [Preadditive.comp_add, ← Category.assoc, ha,
      ← Category.assoc, ← Category.assoc, hiπf, Limits.zero_comp, Limits.zero_comp, add_zero]
  have htρ (n m : ℕ) : t n m ≫ ρ.f m = π.f n ≫ sB.hom n m := by
    dsimp [t]
    rw [Preadditive.add_comp, Category.assoc, hjρf, Limits.comp_zero, zero_add,
      Category.assoc, Category.assoc, hQ, Category.comp_id]
  have htzero (n m : ℕ) (h : ¬ (ComplexShape.up ℕ).Rel m n) : t n m = 0 := by
    simp only [t, a, if_neg h, Limits.zero_comp, sB.zero n m h, Limits.comp_zero, zero_add]
  let F := Homotopy.nullHomotopicMap t
  have hiF : i ≫ F = RZ ≫ j := by
    dsimp only [F]
    rw [Homotopy.comp_nullHomotopicMap]
    simp_rw [hti]
    rw [← Homotopy.nullHomotopicMap_comp, nullHomotopicMap_of_homotopy]
  have hFρ : F ≫ ρ = π ≫ RB := by
    dsimp only [F]
    rw [Homotopy.nullHomotopicMap_comp]
    simp_rw [htρ]
    rw [← Homotopy.comp_nullHomotopicMap, nullHomotopicMap_of_homotopy]
  -- Factor the chain-map defect through the quotient and the target subcomplex.
  let E : I ⟶ JI.cocomplex := RI - F
  have hiE : i ≫ E = 0 := by
    simp only [E, Preadditive.comp_sub, hRi, hiF, sub_self]
  have hEρ : E ≫ ρ = 0 := by
    simp only [E, Preadditive.sub_comp, hRπ, hFρ, sub_self]
  have hScomplex := HomologicalComplex.shortExact_of_degreewise_shortExact
    (ShortComplex.mk i π hiπ) hsource
  have hTcomplex := HomologicalComplex.shortExact_of_degreewise_shortExact
    (ShortComplex.mk j ρ hjρ) htarget
  have : Epi π := hScomplex.epi_g
  have : Mono j := hTcomplex.mono_f
  let y : B ⟶ JI.cocomplex := hScomplex.exact.desc E hiE
  have hy : π ≫ y = E := hScomplex.exact.g_desc E hiE
  have hyρ : y ≫ ρ = 0 := by
    rw [← cancel_epi π, ← Category.assoc, hy, hEρ, Limits.comp_zero]
  let e : B ⟶ JZ.cocomplex := hTcomplex.exact.lift y hyρ
  have he : π ≫ e ≫ j = E := by
    rw [hTcomplex.exact.lift_f, hy]
  have hεId : εI.f 0 ≫ I.d 0 1 = 0 := by
    simp
  have hεIE : εI.f 0 ≫ E.f 0 = 0 := by
    change εI.f 0 ≫ (RI.f 0 - F.f 0) = 0
    rw [Preadditive.comp_sub, hRε₀]
    change 0 - εI.f 0 ≫ (dNext 0 t + prevD 0 t) = 0
    rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
      add_zero, ← Category.assoc, hεId, Limits.zero_comp, sub_self]
  have he₀ : εB.f 0 ≫ e.f 0 = 0 := by
    have := hS.epi_g
    have : Mono (j.f 0) := (htarget 0).mono_f
    rw [← cancel_epi S.g, ← cancel_mono (j.f 0)]
    simp only [Category.assoc, Limits.zero_comp, Limits.comp_zero]
    rw [← Category.assoc S.g, ← hεπ₀, Category.assoc]
    have he0 : π.f 0 ≫ e.f 0 ≫ j.f 0 = E.f 0 := by
      simpa using HomologicalComplex.congr_hom he 0
    rw [he0, hεIE]
  -- A second resolution comparison kills the factored defect.
  let k : Homotopy e 0 := CochainComplex.homotopyZeroOfQuasiIso εB e he₀
  let H := (Homotopy.nullHomotopy t htzero).add ((k.compLeft π).compRight j)
  have hsum : F + (π ≫ e) ≫ j = RI := by
    rw [Category.assoc, he]
    dsimp [E]
    exact add_sub_cancel _ _
  let sI : Homotopy RI 0 :=
    { hom := H.hom
      zero := H.zero
      comm := fun n ↦ by
        have hn := H.comm n
        simpa only [← hsum, HomologicalComplex.zero_f, Limits.comp_zero, Limits.zero_comp,
          HomologicalComplex.add_f_apply, add_zero] using hn }
  have hsI (n m : ℕ) :
      sI.hom n m = t n m + π.f n ≫ k.hom n m ≫ j.f m := by
    exact congrArg (t n m + ·) (Category.assoc _ _ _)
  refine ⟨sI, sB, ?_, ?_, ?_⟩
  · intro m
    have hshape : ¬ (ComplexShape.up ℕ).Rel m 0 := by simp
    exact ⟨sI.zero 0 m hshape, sB.zero 0 m hshape⟩
  · intro n m
    rw [hsI, Preadditive.comp_add, hti, ← Category.assoc, ← Category.assoc,
      hiπf, Limits.zero_comp, Limits.zero_comp, add_zero]
  · intro n m
    rw [hsI, Preadditive.add_comp, htρ, Category.assoc, Category.assoc,
      hjρf, Limits.comp_zero, Limits.comp_zero, add_zero]

end CategoryTheory
