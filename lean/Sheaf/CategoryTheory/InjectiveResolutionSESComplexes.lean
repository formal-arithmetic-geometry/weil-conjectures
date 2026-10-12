/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.CategoryTheory.PushoutShortExactSequence
import Mathlib.Algebra.Homology.ModelCategory.Injective

/-!
# Injective resolutions of short exact sequences of bounded-below complexes

Source: Stacks Project, `derived.tex`, Lemma Tag 013T (lemma-injective-resolution-ses)
(blueprint: lem-weil-pbc-injective-resolution-ses-complexes).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem exists_strict_lift
    {C : Type u} [Category.{v} C] [Abelian C]
    (D I J : CochainComplex C ℤ) (alpha : D ⟶ I) (delta : D ⟶ J)
    (hD : ∀ n : ℤ, n < 0 → IsZero (D.X n))
    (hI : ∀ n : ℤ, n < 0 → IsZero (I.X n))
    (hJ : CochainComplex.plus C J)
    (hJinj : ∀ n : ℤ, Injective (J.X n))
    (hmono : ∀ n : ℤ, Mono (alpha.f n)) (hqis : QuasiIso alpha) :
    ∃ delta' : I ⟶ J, alpha ≫ delta' = delta :=
    by
  let := CochainComplex.Plus.modelCategoryQuillen.instCategoryWithWeakEquivalences (C := C)
  let := CochainComplex.Plus.modelCategoryQuillen.instCategoryWithFibrations (C := C)
  let DP : CochainComplex.Plus C :=
    ⟨D, 0, (CochainComplex.isStrictlyGE_iff D 0).mpr hD⟩
  let IP : CochainComplex.Plus C :=
    ⟨I, 0, (CochainComplex.isStrictlyGE_iff I 0).mpr hI⟩
  let JP : CochainComplex.Plus C := ⟨J, hJ⟩
  let a : DP ⟶ IP := ObjectProperty.homMk alpha
  let d : DP ⟶ JP := ObjectProperty.homMk delta
  have : Mono alpha := HomologicalComplex.mono_of_mono_f _ hmono
  have : Mono a := (CochainComplex.Plus.mono_iff a).mpr this
  have : HomotopicalAlgebra.WeakEquivalence a :=
    (CochainComplex.Plus.modelCategoryQuillen.weakEquivalence_iff a).mpr hqis
  have : HomotopicalAlgebra.IsFibrant JP :=
    (CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff JP).mpr hJinj
  let sq : CommSq d a (terminal.from JP) (terminal.from IP) := ⟨by simp⟩
  exact ⟨sq.lift.hom, congrArg (fun f ↦ f.hom) sq.fac_left⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Construct the twisted biproduct row with prescribed injective ends. The comparison
map is asserted only to be a cochain map with the two commuting squares; its
quasi-isomorphism is a separate consequence of the long exact homology sequences.

Source: Stacks Project, derived.tex, Lemma Tag 013T, proof Step 2, with the kernel
already a complex of injectives and its resolution the identity.
(blueprint: lem-weil-pbc-injective-resolution-ses-complexes)

Proof:
1. Split the row in each degree using injectivity of J, obtaining a retraction r
   and section s with r ≫ i + p ≫ s = identity and s ≫ r = 0.
2. The degree-one maps s^n d_E^n r^(n+1) define the connecting cochain map
   delta : D -> J[1]. Expanding identity = i r + s p on both sides of d_E shows
   that its matrix is (d_J, delta; 0, d_D).
3. The shifted complex J[1] is injective termwise and bounded below at -1.
   Lift delta across the degreewise monomorphic quasi-isomorphism alpha using
   Tag 013P(2), giving delta' : I -> J[1] with alpha delta' = delta.
4. Set K^n = J^n biproduct I^n, with differential matrix (d_J, delta'; 0, d_I).
   Its square is zero because delta' is a cochain map into the shift. Define j
   and q as the first inclusion and second projection. Their chain-map equations
   follow from the diagonal entries, and their row is split short exact.
5. Set psi^n = r^n j^n + p^n alpha^n inr^n. The differential matrix for E and
   alpha delta' = delta imply that psi commutes with differentials. The splitting
   identities give i psi = j and psi q = p alpha. Each K^n is injective as a finite
   biproduct of injectives, and is zero below zero as both summands are zero there.
The zero row and the identity quotient resolution satisfy the same construction;
no inverse to alpha and no splitting by cochain maps is assumed. -/
private theorem exists_injective_kernel_resolution_extension
    {C : Type u} [Category.{v} C] [Abelian C]
    (J E D I : CochainComplex C ℤ) (i : J ⟶ E) (p : E ⟶ D)
    (hJ : ∀ n : ℤ, n < 0 → IsZero (J.X n))
    (hI : ∀ n : ℤ, n < 0 → IsZero (I.X n))
    (hJinj : ∀ n : ℤ, Injective (J.X n))
    (hIinj : ∀ n : ℤ, Injective (I.X n))
    (hip : i ≫ p = 0)
    (hSES : ∀ n : ℤ, ((ShortComplex.mk i p hip).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).ShortExact)
    (alpha : D ⟶ I) (hmono : ∀ n : ℤ, Mono (alpha.f n)) (hqis : QuasiIso alpha)
    (hD : ∀ n : ℤ, n < 0 → IsZero (D.X n)) :
    ∃ (K : CochainComplex C ℤ) (j : J ⟶ K) (q : K ⟶ I) (psi : E ⟶ K),
      (∀ n : ℤ, n < 0 → IsZero (K.X n)) ∧
      (∀ n : ℤ, Injective (K.X n)) ∧
      (∃ hjq : j ≫ q = 0, ∀ n : ℤ, ((ShortComplex.mk j q hjq).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).ShortExact) ∧
      i ≫ psi = j ∧ psi ≫ q = p ≫ alpha := by
  classical
  let S : ShortComplex (CochainComplex C ℤ) := ShortComplex.mk i p hip
  have (n : ℤ) : Injective (J.X n) := hJinj n
  have (n : ℤ) : Injective (I.X n) := hIinj n
  let σ (n : ℤ) : (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting :=
    by
      have hinj : Injective ((S.map
          (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).X₁) := hJinj n
      exact (hSES n).splittingOfInjective
  let r (n : ℤ) : E.X n ⟶ J.X n := (σ n).r
  let s (n : ℤ) : D.X n ⟶ E.X n := (σ n).s
  let delta : D ⟶ J⟦(1 : ℤ)⟧ := CochainComplex.homOfDegreewiseSplit S σ
  have hJGE : J.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff J 0).mpr hJ
  have hJshift : CochainComplex.plus C (J⟦(1 : ℤ)⟧) :=
    ⟨-1, J.isStrictlyGE_shift 0 1 (-1) (by omega)⟩
  have hJshiftinj (n : ℤ) : Injective ((J⟦(1 : ℤ)⟧).X n) := hJinj (n + 1)
  obtain ⟨delta', hdelta'⟩ :=
    exists_strict_lift D I (J⟦(1 : ℤ)⟧) alpha delta hD hI hJshift
      hJshiftinj hmono hqis
  let t (n : ℤ) : I.X n ⟶ J.X (n + 1) := delta'.f n
  have ht (n : ℤ) : t n ≫ J.d (n + 1) (n + 1 + 1) +
      I.d n (n + 1) ≫ t (n + 1) = 0 := by
    have hc := delta'.comm n (n + 1)
    simp only [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_one,
      Units.neg_smul, one_smul, Preadditive.comp_neg] at hc
    change -(t n ≫ J.d (n + 1) (n + 1 + 1)) = I.d n (n + 1) ≫ t (n + 1) at hc
    simpa only [add_neg_cancel] using
      congrArg (fun z ↦ t n ≫ J.d (n + 1) (n + 1 + 1) + z) hc.symm
  have hat (n : ℤ) : alpha.f n ≫ t n =
      s n ≫ E.d n (n + 1) ≫ r (n + 1) := by
    have hc := congrArg (fun f ↦ f.f n) hdelta'
    simpa [t, delta, CochainComplex.homOfDegreewiseSplit_f,
      CochainComplex.cocycleOfDegreewiseSplit] using hc
  let d (n : ℤ) : J.X n ⊞ I.X n ⟶ J.X (n + 1) ⊞ I.X (n + 1) :=
    biprod.fst ≫ J.d n (n + 1) ≫ biprod.inl +
    biprod.snd ≫ t n ≫ biprod.inl + biprod.snd ≫ I.d n (n + 1) ≫ biprod.inr
  have hd (n : ℤ) : d n ≫ d (n + 1) = 0 := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext <;>
        simp [d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    · apply biprod.hom_ext
      · simpa [d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
          using ht n
      · simp [d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
  let K := CochainComplex.of (fun n ↦ J.X n ⊞ I.X n) d hd
  let j : J ⟶ K := CochainComplex.ofHom (fun _ ↦ biprod.inl) (by
    intro n
    simp [K, d, Preadditive.comp_add])
  let q : K ⟶ I := CochainComplex.ofHom (fun _ ↦ biprod.snd) (by
    intro n
    simp [K, d, Preadditive.add_comp, Category.assoc])
  have hrd (n : ℤ) : E.d n (n + 1) ≫ r (n + 1) =
      r n ≫ J.d n (n + 1) + p.f n ≫ alpha.f n ≫ t n := by
    have hid : r n ≫ i.f n + p.f n ≫ s n = 𝟙 (E.X n) := by
      simpa [r, s, S] using (σ n).id
    have hr : i.f (n + 1) ≫ r (n + 1) = 𝟙 (J.X (n + 1)) := by
      simpa [r, S] using (σ (n + 1)).f_r
    calc
      E.d n (n + 1) ≫ r (n + 1) =
          (r n ≫ i.f n + p.f n ≫ s n) ≫ E.d n (n + 1) ≫ r (n + 1) := by
        rw [hid, Category.id_comp]
      _ = r n ≫ J.d n (n + 1) + p.f n ≫ alpha.f n ≫ t n := by
        simp only [Preadditive.add_comp, Category.assoc, i.comm_assoc, hr,
          Category.comp_id, ← hat n]
  let psi : E ⟶ K := CochainComplex.ofHom
    (fun n ↦ r n ≫ biprod.inl + p.f n ≫ alpha.f n ≫ biprod.inr) (by
      intro n
      apply biprod.hom_ext
      · simpa [K, d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
          using (hrd n).symm
      · simp [K, d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
          p.comm_assoc])
  have hjq : j ≫ q = 0 := by ext n; simp [j, q]
  refine ⟨K, j, q, psi, ?_, ?_, ⟨hjq, ?_⟩, ?_, ?_⟩
  · intro n hn
    exact (biprod_isZero_iff _ _).mpr ⟨hJ n hn, hI n hn⟩
  · intro n
    change Injective (J.X n ⊞ I.X n)
    infer_instance
  · intro n
    exact (ShortComplex.Splitting.ofHasBinaryBiproduct (J.X n) (I.X n)).shortExact
  · have hir (n : ℤ) : i.f n ≫ r n = 𝟙 (J.X n) := by
      simpa [r, S] using (σ n).f_r
    have hipf (n : ℤ) : i.f n ≫ p.f n = 0 := by
      simpa using congrArg (fun f ↦ f.f n) hip
    ext n <;> simp [psi, j, Preadditive.comp_add, Category.assoc, hir, reassoc_of% hipf n]
  · ext n
    simp [psi, q, Preadditive.add_comp, Category.assoc]


/-- In an abelian category with enough injectives, a degreewise short exact sequence of
bounded-below cochain complexes admits compatible injective resolutions.

Source: Stacks Project, `derived.tex`, Lemma Tag 013T, line 6571, main assertion and
part (2); injective resolutions of complexes are as in Section Tag 013G.

Proof (the eleven steps of the DAG node, expanding Stacks proof Steps 1--2):
1. Resolve A by a complex I₁ of injectives vanishing below zero, with quasi-isomorphism
   φ₁, using lem-weil-pbc-complex-injective-resolution-mono at lower bound zero.
2. By lem-weil-pbc-cochain-complexes-degreewise-exact, form the pushout along φ₁ in
   the abelian category of complexes (lem-weil-pbc-pushout-short-exact-sequence).
   Obtain I₁ → E → D, with maps ι, p and v : B → E. The row is degreewise short exact,
   v f = ι φ₁, p v = g, and E vanishes below zero since I₁ and D do.
3. The long exact cohomology sequences (lem-weil-pbc-complex-ses-homology-long-exact)
   and their naturality (lem-weil-pbc-complex-ses-long-exact-naturality) give a morphism
   of long exact sequences with outer vertical maps φ₁ and the identity of D.
   The five lemma (lem-weil-pbc-five-lemma) shows that v is a quasi-isomorphism.
4. Split I₁ⁿ → Eⁿ → Dⁿ using lem-weil-pbc-ses-injective-kernel-splits. Choose π and s
   with πι = id, ps = id, ιπ + sp = id and πs = 0.
5. By lem-weil-pbc-degreewise-split-connecting-morphism, δⁿ = πⁿ⁺¹ d_Eⁿ sⁿ defines
   δ : D → I₁[1], and in the splitting the differential of E has diagonal entries
   d_I₁, d_D and upper-right entry δ.
6. Resolve D by a degreewise monomorphic quasi-isomorphism f₃ : D → I₃, with I₃
   injective and zero below zero (lem-weil-pbc-complex-injective-resolution-mono).
7. Resolve I₁ by itself. The bounded-below injective complex I₁[1] admits a lift
   δ' : I₃ → I₁[1] with δ' f₃ = δ by lem-weil-pbc-lift-along-injective-quasi-iso.
8. Define I₂ⁿ = I₁ⁿ ⊞ I₃ⁿ with differential matrix (d_I₁, δ'; 0, d_I₃). Its square
   is zero because δ' is a cochain map to the shift. Its terms are injective by
   lem-weil-pbc-product-injectives and vanish below zero. The inclusion j and
   projection q are cochain maps and form short exact rows (def-sp-abelian).
9. Set ψⁿ = jⁿ πⁿ + εⁿ f₃ⁿ pⁿ, where ε is the second inclusion. The matrix formula
   and δ' f₃ = δ make ψ : E → I₂ a cochain map with ψι = j and qψ = f₃p.
10. Apply lem-weil-pbc-complex-ses-homology-long-exact and
    lem-weil-pbc-complex-ses-long-exact-naturality to (id, ψ, f₃). The outer maps
    on cohomology are isomorphisms, so lem-weil-pbc-five-lemma makes ψ a quasi-isomorphism.
11. Put φ₂ = ψv and φ₃ = f₃. Composition preserves the cohomology isomorphisms;
    φ₂f = jφ₁ and qφ₂ = φ₃g follow from the pushout and ψ identities. The three
    complexes and the degreewise short exact row have the required properties.
(blueprint: lem-weil-pbc-injective-resolution-ses-complexes). -/
theorem exists_injective_resolution_ses_complexes
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (A B D : CochainComplex C ℤ)
    (f : A ⟶ B) (g : B ⟶ D)
    (hA : ∀ n : ℤ, n < 0 → IsZero (A.X n))
    (hB : ∀ n : ℤ, n < 0 → IsZero (B.X n))
    (hD : ∀ n : ℤ, n < 0 → IsZero (D.X n))
    (hSES : ∃ hfg : f ≫ g = 0, ∀ n : ℤ,
      ((ShortComplex.mk f g hfg).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).ShortExact) :
    ∃ (I₁ I₂ I₃ : CochainComplex C ℤ)
      (j : I₁ ⟶ I₂) (q : I₂ ⟶ I₃)
      (φ₁ : A ⟶ I₁) (φ₂ : B ⟶ I₂) (φ₃ : D ⟶ I₃),
      (∀ n : ℤ, n < 0 → IsZero (I₁.X n)) ∧
      (∀ n : ℤ, n < 0 → IsZero (I₂.X n)) ∧
      (∀ n : ℤ, n < 0 → IsZero (I₃.X n)) ∧
      (∀ n : ℤ, Injective (I₁.X n)) ∧
      (∀ n : ℤ, Injective (I₂.X n)) ∧
      (∀ n : ℤ, Injective (I₃.X n)) ∧
      (∃ hjq : j ≫ q = 0, ∀ n : ℤ,
        ((ShortComplex.mk j q hjq).map
          (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).ShortExact) ∧
      QuasiIso φ₁ ∧ QuasiIso φ₂ ∧ QuasiIso φ₃ ∧
      f ≫ φ₂ = φ₁ ≫ j ∧ g ≫ φ₃ = φ₂ ≫ q := by
  -- The middle bound follows from the exact row and the outer bounds; retain the input.
  have _hB := hB
  obtain ⟨I₁, φ₁, hI₁, hI₁inj, _, hφ₁⟩ :=
    CochainComplex.exists_mono_quasiIso_injective_boundedBelow C 0 A hA
  obtain ⟨I₃, φ₃, hI₃, hI₃inj, hφ₃mono, hφ₃⟩ :=
    CochainComplex.exists_mono_quasiIso_injective_boundedBelow C 0 D hD
  obtain ⟨hfg, hrows⟩ := hSES
  let S : ShortComplex (CochainComplex C ℤ) := ShortComplex.mk f g hfg
  have hS : S.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact S hrows
  obtain ⟨_, p, hip, hvp, _, hT, F, hF₁, hF₂, hF₃⟩ :=
    pushout_short_exact_sequence S hS φ₁
  let E := pushout φ₁ f
  let i : I₁ ⟶ E := pushout.inl φ₁ f
  let v : B ⟶ E := pushout.inr φ₁ f
  let T : ShortComplex (CochainComplex C ℤ) := ShortComplex.mk i p hip
  have hTrows := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).mp hT
  have hv : QuasiIso v := by
    have h₁ : QuasiIso F.τ₁ := by rw [hF₁]; exact hφ₁
    have h₃ : QuasiIso F.τ₃ := by rw [hF₃]; infer_instance
    simpa only [hF₂] using HomologicalComplex.HomologySequence.quasiIso_τ₂ F hS hT h₁ h₃
  obtain ⟨I₂, j, q, ψ, hI₂, hI₂inj, ⟨hjq, hIrows⟩, hiψ, hψq⟩ :=
    exists_injective_kernel_resolution_extension I₁ E D I₃ i p hI₁ hI₃
      hI₁inj hI₃inj hip hTrows φ₃ hφ₃mono hφ₃ hD
  let U : ShortComplex (CochainComplex C ℤ) := ShortComplex.mk j q hjq
  have hU := HomologicalComplex.shortExact_of_degreewise_shortExact U hIrows
  let G : T ⟶ U :=
    { τ₁ := 𝟙 I₁
      τ₂ := ψ
      τ₃ := φ₃
      comm₁₂ := by simpa [T, U] using hiψ.symm
      comm₂₃ := hψq }
  have hψ : QuasiIso ψ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₂ G hT hU (by dsimp [G]; infer_instance) hφ₃
  have hφ₂ : QuasiIso (v ≫ ψ) := by
    have := hv
    have := hψ
    infer_instance
  refine ⟨I₁, I₂, I₃, j, q, φ₁, v ≫ ψ, φ₃, hI₁, hI₂, hI₃,
    hI₁inj, hI₂inj, hI₃inj, ⟨hjq, hIrows⟩, hφ₁, hφ₂, hφ₃, ?_, ?_⟩
  · rw [← Category.assoc, ← pushout.condition, Category.assoc, hiψ]
  · rw [Category.assoc, hψq, ← Category.assoc, hvp]

end CategoryTheory
