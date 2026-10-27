/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Sheaf.Paper.ClopenIntegralRestriction
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Paper.AugmentedIntegralDescentCore
import all Sheaf.Paper.AugmentedIntegralDescentCore
import Sheaf.Paper.IntegralReductionFiniteClopenBounds
import Mathlib.Data.Fintype.Lattice

/-! # Augmented integral membership and uniform bounds

Source: Bhatt--Scholze, Proposition 3.5.1(1) and Definition 3.5.2, p. 24
(blueprint: lem-pur-clopen-augmented-integral-descent).

The ordinary restriction, augmented reduction and normalized Roos support are
publicly re-exported from the compilation support module with their original names.
-/

@[expose] public noncomputable section
-- Keep the fixed coefficient-universe abelian structure.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
-- Avoid repeated unused-instance scans of the large normalized comparison types.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.unrestrictedIntegralReductionExistence

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})
  (X : Over (Spec (CommRingCat.of P.field.k)))
  [hft : LocallyOfFiniteType X.hom] [hqc : QuasiCompact X.hom]
  {I : Type w} [hfinite : Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i i', i ≠ i' →
    Disjoint (Set.range (j i).left) (Set.range (j i').left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hft hqc hfinite hclosed hdisjoint hcover

attribute [local irreducible] clopenIntegralModuleRestriction clopenIntegralDerivedRestriction
  scalarReductionDerivedExtension completedIntegralCommRingSheafUnrestricted

set_option maxHeartbeats 800000 in
-- Elaborating the normalized scalar and localization comparisons requires extra heartbeats.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived in
/-- Completeness, integral membership, and intervals uniform over every positive
reduction are detected on the components. Finite extrema give common intervals;
the same assertion allows every common larger interval. Empty components are zero,
and the empty partition has all three membership properties with interval [0,0].
Source: Bhatt--Scholze, Definition 3.5.2 and Proposition 3.5.1(1), p. 24
(blueprint: lem-pur-clopen-augmented-integral-descent).

Proof (node steps 4-7): a completing connecting map restricts to completing maps.
Conversely the Hom bijection in step 3 lifts any tuple of completing maps, and
reflection of distinguishedness gives completeness with the actual augmentation.
At each positive level apply lem-pur-clopen-finite-constructibility-bounds to the
reduction comparison: constructibility, support in a fixed interval and Tor amplitude
in a fixed interval are detected componentwise. Quantify over every level without
changing the interval. For a finite nonempty partition take the minimum of lower
bounds and maximum of upper bounds; containment of intervals preserves both vanishing
conditions. Combine completeness and the uniform bounds to obtain both integral
membership equivalences. On an empty component the derived category is zero. If the
partition is empty, covering forces X empty, and its zero objects meet completeness,
constructibility and every ordered support and Tor interval, in particular [0,0]. -/
theorem augmentedIntegralMembershipBounds
    (K : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left)) :
    (IntegralOnSlice.IsComplete P.coefficients.l P.extension X.left none K ↔
      ∀ i, IntegralOnSlice.IsComplete P.coefficients.l P.extension (Xi i).left none
        ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ∧
    (sfIntegralConstructible P.coefficients.l P.extension X.left K ↔
      ∀ i, sfIntegralConstructible P.coefficients.l P.extension (Xi i).left
        ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ∧
    (finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K ↔
      ∀ i, finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left
        ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
            Set.Icc a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ⊆
              Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K))
          a b)) ∧
    (∀ a b : I → ℤ, (∀ i, a i ≤ b i) →
      (Nonempty I → ∃ A B : ℤ,
        (∃ i, A = a i) ∧ (∀ i, A ≤ a i) ∧
        (∃ i, B = b i) ∧ (∀ i, b i ≤ B) ∧ A ≤ B ∧
        ((∀ (i : I) (n : ℕ), proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).obj K)) ⊆ Set.Icc (a i) (b i)) →
          ∀ n : ℕ, proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
              Set.Icc A B) ∧
        ((∀ (i : I) (n : ℕ), HasProEtaleTorAmplitude (Xi i).left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).obj K)) (a i) (b i)) →
          ∀ n : ℕ, HasProEtaleTorAmplitude X.left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) A B)) ∧
      ∀ A B : ℤ, A ≤ B → (∀ i, A ≤ a i) → (∀ i, b i ≤ B) →
        ((∀ (i : I) (n : ℕ), proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).obj K)) ⊆ Set.Icc (a i) (b i)) →
          ∀ n : ℕ, proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
              Set.Icc A B) ∧
        ((∀ (i : I) (n : ℕ), HasProEtaleTorAmplitude (Xi i).left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).obj K)) (a i) (b i)) →
          ∀ n : ℕ, HasProEtaleTorAmplitude X.left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) A B)) ∧
    (∀ i, IsEmpty (Xi i).left → ∀ L : DerivedCategory
        (scalarReductionSource P.coefficients.l P.extension (Xi i).left), IsZero L) ∧
    (IsEmpty I → IsEmpty X.left ∧
      (∀ L : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left),
        IsZero L) ∧
      IntegralOnSlice.IsComplete P.coefficients.l P.extension X.left none K ∧
      sfIntegralConstructible P.coefficients.l P.extension X.left K ∧
      finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K ∧
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
          Set.Icc 0 0) ∧
      (∀ n : ℕ, HasProEtaleTorAmplitude X.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) 0 0)) := by
  classical
  let r (i : I) := clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left
  have hlevel (n : ℕ) :=
    integralReductionFiniteClopenBounds P X Xi j hdisjoint hcover K n
  have hs (a b : ℤ) (hab : a ≤ b) :
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
          Set.Icc a b) ↔
      ∀ (i : I) (n : ℕ), proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
          ((r i).obj K)) ⊆ Set.Icc a b := by
    constructor
    · intro h i n
      exact ((hlevel n).2.1 a b hab).mp (h n) i
    · intro h n
      exact ((hlevel n).2.1 a b hab).mpr (fun i ↦ h i n)
  have ht (a b : ℤ) (hab : a ≤ b) :
      (∀ n : ℕ, HasProEtaleTorAmplitude X.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) a b) ↔
      ∀ (i : I) (n : ℕ), HasProEtaleTorAmplitude (Xi i).left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
          ((r i).obj K)) a b := by
    constructor
    · intro h i n
      exact ((hlevel n).2.2 a b hab).mp (h n) i
    · intro h n
      exact ((hlevel n).2.2 a b hab).mpr (fun i ↦ h i n)
  have hc : IsSfDerivedComplete P.coefficients.l P.extension X.left K ↔
      ∀ i, IsSfDerivedComplete P.coefficients.l P.extension (Xi i).left ((r i).obj K) := by
    obtain ⟨⟨hp⟩, hpi, hd⟩ := augmentedIntegralRoosDescent P X Xi j hdisjoint hcover K
    let := hp
    let hp' (i : I) := (hpi i).some
    let : ∀ i, HasCountableProducts
        (DerivedCategory (scalarReductionSource P.coefficients.l P.extension (Xi i).left)) := hp'
    obtain ⟨α, _, hb, hδ⟩ := hd
    constructor
    · rintro ⟨_, δ, hδK⟩ i
      exact ⟨inferInstance, _, (hδ δ).mp hδK i⟩
    · intro h
      choose hp δ hh using h
      obtain ⟨δ', hδ'⟩ := hb.surjective δ
      refine ⟨inferInstance, δ', (hδ δ').mpr ?_⟩
      intro i
      simpa only [congrFun hδ' i] using hh i
  have hext (a b : I → ℤ) (hab : ∀ i, a i ≤ b i) [Nonempty I] :
      ∃ A B : ℤ, (∃ i, A = a i) ∧ (∀ i, A ≤ a i) ∧
        (∃ i, B = b i) ∧ (∀ i, b i ≤ B) ∧ A ≤ B := by
    obtain ⟨i, hi⟩ := Finite.exists_min a
    obtain ⟨k, hk⟩ := Finite.exists_max b
    exact ⟨a i, b k, ⟨i, rfl⟩, hi, ⟨k, rfl⟩, hk, (hab i).trans (hk i)⟩
  have hsMono (a b : I → ℤ) (A B : ℤ) (hAB : A ≤ B)
      (ha : ∀ i, A ≤ a i) (hb : ∀ i, b i ≤ B) :
      (∀ (i : I) (n : ℕ), proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
          ((r i).obj K)) ⊆ Set.Icc (a i) (b i)) →
      ∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
          Set.Icc A B := by
    intro h
    apply (hs A B hAB).mpr
    intro i n m hm
    exact ⟨(ha i).trans (h i n hm).1, (h i n hm).2.trans (hb i)⟩
  have htMono (a b : I → ℤ) (A B : ℤ) (hAB : A ≤ B)
      (ha : ∀ i, A ≤ a i) (hb : ∀ i, b i ≤ B) :
      (∀ (i : I) (n : ℕ), HasProEtaleTorAmplitude (Xi i).left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
          ((r i).obj K)) (a i) (b i)) →
      ∀ n : ℕ, HasProEtaleTorAmplitude X.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) A B := by
    intro h
    apply (ht A B hAB).mpr
    intro i n
    exact torBounds_mono _ _ _ (h i n) hAB (ha i) (hb i)
  have hcst : sfIntegralConstructible P.coefficients.l P.extension X.left K ↔
      ∀ i, sfIntegralConstructible P.coefficients.l P.extension (Xi i).left ((r i).obj K) := by
    constructor
    · rintro ⟨hK, a, b, hab, hn⟩ i
      refine ⟨hc.mp hK i, a, b, hab, ?_⟩
      intro n
      exact ⟨(hlevel n).1.mp (hn n).1 i, (hs a b hab).mp (fun n ↦ (hn n).2) i n⟩
    · intro h
      refine ⟨hc.mpr (fun i ↦ (h i).1), ?_⟩
      by_cases hi : Nonempty I
      · let := hi
        choose a b hab hn using fun i ↦ (h i).2
        obtain ⟨A, B, _, hA, _, hB, hAB⟩ := hext a b hab
        refine ⟨A, B, hAB, fun n ↦ ⟨?_, ?_⟩⟩
        · exact (hlevel n).1.mpr (fun i ↦ (hn i n).1)
        · exact hsMono a b A B hAB hA hB (fun i n ↦ (hn i n).2) n
      · have : IsEmpty I := not_nonempty_iff.mp hi
        exact ⟨0, 0, le_refl _, fun n ↦
          ⟨(hlevel n).1.mpr (fun i ↦ isEmptyElim i),
            (hs 0 0 (le_refl _)).mpr (fun i ↦ isEmptyElim i) n⟩⟩
  have hctf : finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K ↔
      ∀ i, finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left
        ((r i).obj K) := by
    constructor
    · rintro ⟨hK, a, b, hab, hn⟩ i
      exact ⟨hcst.mp hK i, a, b, hab, (ht a b hab).mp hn i⟩
    · intro h
      refine ⟨hcst.mpr (fun i ↦ (h i).1), ?_⟩
      by_cases hi : Nonempty I
      · let := hi
        choose a b hab hn using fun i ↦ (h i).2
        obtain ⟨A, B, _, hA, _, hB, hAB⟩ := hext a b hab
        exact ⟨A, B, hAB, htMono a b A B hAB hA hB hn⟩
      · have : IsEmpty I := not_nonempty_iff.mp hi
        exact ⟨0, 0, le_refl _, (ht 0 0 (le_refl _)).mpr (fun i ↦ isEmptyElim i)⟩
  refine ⟨?_, hcst, hctf, hs, ht, ?_, ?_, ?_⟩
  · rw [← intrinsicComplete_iff _ _ P.field P.coefficients.different]
    exact hc.trans (forall_congr' (fun i ↦
      intrinsicComplete_iff _ _ P.field P.coefficients.different _ _))
  · intro a b hab
    refine ⟨?_, fun A B hAB hA hB ↦
      ⟨hsMono a b A B hAB hA hB, htMono a b A B hAB hA hB⟩⟩
    intro hi
    let := hi
    obtain ⟨A, B, ha, hA, hb, hB, hAB⟩ := hext a b hab
    exact ⟨A, B, ha, hA, hb, hB, hAB,
      hsMono a b A B hAB hA hB, htMono a b A B hAB hA hB⟩
  · intro i hi L
    let := hi
    exact emptyIntegral_zero _ _ _ L
  · intro hi
    let := hi
    have hX : IsEmpty X.left := ⟨fun x ↦ by
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
      exact isEmptyElim i⟩
    let := hX
    refine ⟨hX, fun L ↦ emptyIntegral_zero _ _ _ L, ?_, ?_, ?_, ?_, ?_⟩
    · exact (intrinsicComplete_iff _ _ P.field P.coefficients.different _ _).mp
        (hc.mpr (fun i ↦ isEmptyElim i))
    · exact hcst.mpr (fun i ↦ isEmptyElim i)
    · exact hctf.mpr (fun i ↦ isEmptyElim i)
    · exact (hs 0 0 (le_refl _)).mpr (fun i ↦ isEmptyElim i)
    · exact (ht 0 0 (le_refl _)).mpr (fun i ↦ isEmptyElim i)


end WeilConjectures.PurityFiniteSetting
