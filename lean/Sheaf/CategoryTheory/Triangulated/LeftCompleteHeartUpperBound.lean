/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.Algebra.Homology.LowerTruncationStepTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# Upper cohomological bounds from the heart and left completeness

Source: Stacks Project, Derived Categories, Tags 08TB, 08TC, 07KC and 0H72;
Weil conjectures blueprint, det-prop-int-compactness-direct-sums, proof (2)
(blueprint: lem-sfb-left-complete-heart-upper-bound).
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

private lemma tower_difference_solution
    {C : Type*} [Category C] [Preadditive C] {X : ℕ → C}
    (f : ∀ n, X (n + 1) ⟶ X n) (N : ℕ) (hf : ∀ n, N ≤ n → IsIso (f n))
    (Q : C) (p : ∀ n, Q ⟶ X n) :
    ∃ v : ∀ n, Q ⟶ X n, ∀ n, v n - v (n + 1) ≫ f n = p n := by
  induction N generalizing X with
  | zero =>
    have (n : ℕ) : IsIso (f n) := hf n (Nat.zero_le n)
    let v : ∀ n, Q ⟶ X n :=
      fun n ↦ Nat.recOn n 0 (fun n a ↦ (a - p n) ≫ inv (f n))
    refine ⟨v, fun n ↦ ?_⟩
    change v n - ((v n - p n) ≫ inv (f n)) ≫ f n = p n
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    abel
  | succ N ih =>
    obtain ⟨w, hw⟩ := ih (fun n ↦ f (n + 1))
      (fun n hn ↦ hf (n + 1) (by omega)) (fun n ↦ p (n + 1))
    let v : ∀ n, Q ⟶ X n
      | 0 => p 0 + w 0 ≫ f 0
      | n + 1 => w n
    refine ⟨v, fun n ↦ ?_⟩
    cases n with
    | zero => dsimp [v]; abel
    | succ n => exact hw n

private lemma epi_map_towerTransitionEndomorphism
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X : ℕ → C} [HasProduct X]
    [PreservesLimit (Discrete.functor X) F]
    (f : ∀ n, X (n + 1) ⟶ X n)
    (h : ∃ N : ℕ, ∀ n, N ≤ n → IsIso (F.map (f n))) :
    Epi (F.map (towerTransitionEndomorphism f)) := by
  let P := F.obj (∏ᶜ X)
  let p (n : ℕ) : P ⟶ F.obj (X n) := F.map (Pi.π X n)
  let hP := isLimitFanMkObjOfIsLimit F X (Pi.π X) (productIsProduct X)
  obtain ⟨N, hN⟩ := h
  obtain ⟨v, hv⟩ := tower_difference_solution (fun n ↦ F.map (f n)) N hN P p
  let s : P ⟶ P := Fan.IsLimit.lift hP v
  have hsπ (n : ℕ) : s ≫ F.map (Pi.π X n) = v n := Fan.IsLimit.fac hP v n
  have hs : s ≫ F.map (towerTransitionEndomorphism f) = 𝟙 P := by
    apply Fan.IsLimit.hom_ext hP
    intro n
    change (s ≫ F.map (towerTransitionEndomorphism f)) ≫ p n = 𝟙 P ≫ p n
    simp only [Category.assoc, p, ← F.map_comp]
    rw [(towerTransitionEndomorphism_eq_iff f _).mp rfl n]
    simp only [Functor.map_sub, Functor.map_comp, Preadditive.comp_sub,
      ← Category.assoc, hsπ, Category.id_comp]
    exact hv n
  have : IsSplitEpi (F.map (towerTransitionEndomorphism f)) := ⟨⟨⟨s, hs⟩⟩⟩
  infer_instance

/-- A uniform upper bound on a class of heart objects extends to bounded above objects
whose cohomology belongs to that class, using left completeness and preservation of
countable products. The left-completeness hypothesis is independent of the product
witness, whose existence follows from exact countable products.
Source: Stacks Project, Tags 08TB, 08TC, 07KC and 0H72, and blueprint
`det-prop-int-compactness-direct-sums`, proof (2)
(blueprint: lem-sfb-left-complete-heart-upper-bound).

Proof:
1. Exactness and the shift/cohomology isomorphism (lem-sp-derived-cohomology-shift)
show that the image of `H^i(K)[-i]` is bounded above by `i + c`.
2. Induct on `b + 1 - a`, starting from the zero truncation at `a = b + 1`.
The lower-truncation triangle (lem-pc-derived-lower-truncation-step-triangle)
and its image long exact sequence (lem-sf-derived-homology-long-exact) give the
bound `b + c` for every `T(tau_(>=a) K)`. Truncations with `a > b` are zero.
3. The successive tower layer is `H^(-n-1)(K)[n+1]`, whose image is bounded above
by `c - n - 1`. Its long exact sequence makes the transition on degree `r`
cohomology invertible for every sufficiently large `n`, namely `n >= max(0,c-r)`.
4. Exact countable products give derived products and compatibility of cohomology
with their projections (lem-weil-derived-limit-products-core). Left completeness
supplies the canonical Roos triangle of `K`. Apply `T` to this distinguished
triangle directly. Preservation makes the mapped product projection fan limiting,
so all subsequent arguments take place on the mapped product itself.
5. For `j > b + c`, its long exact sequence and the product compatibility give
an exact segment from `1-s` on the product of degree `j-1` cohomology, through
`H^j(TK)`, to the zero product of degree `j` cohomology. It suffices that `1-s`
on the former product be an epimorphism.
6. Write this cohomology tower as `(A_n,f_n)` and choose `N` beyond which `f_n`
is invertible. On `Q = product A_n`, with projections `p_n`, put `v_N = 0`.
Define backwards `v_n = p_n + v_(n+1) >> f_n` for `n < N`, and forwards
`v_(n+1) = (v_n - p_n) >> inverse(f_n)` for `n >= N`. Every component is a finite
expression. The universal property gives `v : Q --> Q` with
`v >> (1-s) = identity`. Thus `1-s` is a split epimorphism, without enough
injectives or any elementwise argument.
7. Exactness of the segment in step 5 now gives `H^j(TK) = 0`. This uses only
finite truncation intervals and eventual invertibility to handle the negative tail;
no lower bound on `K` or on the functor is used. -/
theorem upperBound_of_heart_of_leftComplete
    (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (B : Type uB) [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    [HasCountableProducts A] [CountableAB4Star A]
    [HasCountableProducts B] [CountableAB4Star B]
    (hcomplete : ∀ (K : DerivedCategory A)
      [HasProduct (fun n : ℕ ↦ (TStructure.t.truncGE (-(n : ℤ))).obj K)],
      ∃ δ : (∏ᶜ (fun n : ℕ ↦ (TStructure.t.truncGE (-(n : ℤ))).obj K)) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ (TStructure.t.natTransTruncGEOfLE
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app K)
          K (Pi.lift (fun n : ℕ ↦ (TStructure.t.truncGEπ (-(n : ℤ))).app K)) δ)
    (T : DerivedCategory A ⥤ DerivedCategory B) [T.CommShift ℤ] [T.IsTriangulated]
    [∀ (I : Type) [Countable I], PreservesLimitsOfShape (Discrete I) T]
    (S : Set A) (c : ℤ)
    (hheart : ∀ M : A, M ∈ S → ∀ j : ℤ, c < j →
      IsZero ((homologyFunctor B j).obj (T.obj ((singleFunctor A 0).obj M))))
    (b : ℤ) (K : DerivedCategory A)
    (hS : ∀ i : ℤ, (homologyFunctor A i).obj K ∈ S)
    (hbound : ∀ i : ℤ, b < i → IsZero ((homologyFunctor A i).obj K)) :
    ∀ j : ℤ, b + c < j → IsZero ((homologyFunctor B j).obj (T.obj K)) := by
  have hLayer (i : ℤ) :
      (T.obj (((singleFunctor A 0).obj ((homologyFunctor A i).obj K))⟦-i⟧)).IsLE
        (i + c) := by
    have hH : (T.obj ((singleFunctor A 0).obj ((homologyFunctor A i).obj K))).IsLE c :=
      (isLE_iff _ _).mpr (hheart _ (hS i))
    have hshift : ((T.obj ((singleFunctor A 0).obj
        ((homologyFunctor A i).obj K)))⟦-i⟧).IsLE (i + c) :=
      TStructure.t.isLE_shift
      (T.obj ((singleFunctor A 0).obj ((homologyFunctor A i).obj K))) c (-i)
        (i + c) (by omega)
    let e : (T.obj ((singleFunctor A 0).obj ((homologyFunctor A i).obj K)))⟦-i⟧ ≅
        T.obj (((singleFunctor A 0).obj ((homologyFunctor A i).obj K))⟦-i⟧) :=
      (T.commShiftIso (-i)).symm.app _
    exact TStructure.t.isLE_of_iso e _
  have hK : K.IsLE b := (isLE_iff K b).mpr hbound
  have hTrunc : ∀ n : ℕ, ∀ a : ℤ, b + 1 - a = n →
      (T.obj ((TStructure.t.truncGE a).obj K)).IsLE (b + c) := by
    intro n
    induction n with
    | zero =>
      intro a ha
      have heq : a = b + 1 := by omega
      subst a
      exact TStructure.t.isLE_of_isZero
        (T.map_isZero (TStructure.t.isZero_truncGE_obj_of_isLE b (b + 1) rfl K)) _
    | succ n ih =>
      intro a ha
      obtain ⟨f, δ, hΔ⟩ := exists_lowerTruncationStepTriangle K (-a)
      have hΔ' := T.map_distinguished _ hΔ
      have h₁ : (T.obj ((Q.obj ((CochainComplex.singleFunctor A 0).obj
          ((homologyFunctor A (-(-a))).obj K)))⟦-a⟧)).IsLE (b + c) := by
        simp only [neg_neg]
        change (T.obj (((singleFunctor A 0).obj
          ((homologyFunctor A a).obj K))⟦-a⟧)).IsLE (b + c)
        have hL := hLayer a
        exact TStructure.t.isLE_of_le _ (a + c) (b + c) (by omega)
      have h₃ := ih (a + 1) (by omega)
      have h₂ := TStructure.t.isLE₂ _ hΔ' (b + c) h₁ (by simpa using h₃)
      simpa using h₂
  have hTruncAll (a : ℤ) : (T.obj ((TStructure.t.truncGE a).obj K)).IsLE (b + c) := by
    by_cases ha : a ≤ b + 1
    · exact hTrunc (b + 1 - a).toNat a (by omega)
    · have hK' : K.IsLE (a - 1) := TStructure.t.isLE_of_le K b _ (by omega)
      exact TStructure.t.isLE_of_isZero
        (T.map_isZero (TStructure.t.isZero_truncGE_obj_of_isLE (a - 1) a (by omega) K)) _
  let X (n : ℕ) : DerivedCategory A := (TStructure.t.truncGE (-(n : ℤ))).obj K
  let u (n : ℕ) : X (n + 1) ⟶ X n :=
    (TStructure.t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
      (by omega)).app K
  have hstable (r : ℤ) : ∃ N : ℕ, ∀ n, N ≤ n →
      IsIso ((homologyFunctor B r).map (T.map (u n))) := by
    refine ⟨(c - r).toNat, fun n hn ↦ ?_⟩
    obtain ⟨f, δ, hΔ⟩ := exists_lowerTruncationStepTriangle K ((n : ℤ) + 1)
    let Δ := T.mapTriangle.obj (CategoryTheory.Pretriangulated.Triangle.mk f
      ((TStructure.t.natTransTruncGEOfLE (-((n : ℤ) + 1))
        (-((n : ℤ) + 1) + 1) (by omega)).app K) δ)
    have hΔ' : Δ ∈ distTriang _ := T.map_distinguished _ hΔ
    have hL : Δ.obj₁.IsLE (-((n : ℤ) + 1) + c) := by
      change (T.obj ((Q.obj ((CochainComplex.singleFunctor A 0).obj
        ((homologyFunctor A (-((n : ℤ) + 1))).obj K)))⟦(n : ℤ) + 1⟧)).IsLE _
      change (T.obj (((singleFunctor A 0).obj
        ((homologyFunctor A (-((n : ℤ) + 1))).obj K))⟦(n : ℤ) + 1⟧)).IsLE _
      simpa only [neg_neg] using hLayer (-((n : ℤ) + 1))
    have hz₀ := isZero_of_isLE Δ.obj₁ (-((n : ℤ) + 1) + c) r (by omega)
    have hz₁ := isZero_of_isLE Δ.obj₁ (-((n : ℤ) + 1) + c) (r + 1) (by omega)
    have hm : Mono ((homologyFunctor B r).map Δ.mor₂) :=
      (HomologySequence.mono_homologyMap_mor₂_iff Δ hΔ' r).mpr
        (hz₀.eq_of_src _ _)
    have he : Epi ((homologyFunctor B r).map Δ.mor₂) :=
      (HomologySequence.epi_homologyMap_mor₂_iff Δ hΔ' r (r + 1) rfl).mpr
        (hz₁.eq_of_tgt _ _)
    have hiso := isIso_of_mono_of_epi ((homologyFunctor B r).map Δ.mor₂)
    change IsIso ((homologyFunctor B r).map (T.map
      ((TStructure.t.natTransTruncGEOfLE (-((n : ℤ) + 1))
        (-((n : ℤ) + 1) + 1) (by omega)).app K))) at hiso
    have htransport (a d : ℤ) (had : a ≤ d)
        (ha : a = -((n : ℤ) + 1)) (hd : d = -((n : ℤ) + 1) + 1) :
        IsIso ((homologyFunctor B r).map
          (T.map ((TStructure.t.natTransTruncGEOfLE a d had).app K))) := by
      subst a
      subst d
      exact hiso
    exact htransport _ _ _ (by omega) (by omega)
  obtain ⟨hPA, _, hHA⟩ := derivedCategory_countableProducts_core.{0} A
  obtain ⟨hPB, _, hHB⟩ := derivedCategory_countableProducts_core.{0} B
  have (r : ℤ) : PreservesLimitsOfShape (Discrete ℕ) (homologyFunctor B r) := hHB ℕ r
  obtain ⟨δ, hδ⟩ := hcomplete K
  let Δ := T.mapTriangle.obj (CategoryTheory.Pretriangulated.Triangle.mk
    (Pi.lift (fun n : ℕ ↦ (TStructure.t.truncGEπ (-(n : ℤ))).app K))
    (towerTransitionEndomorphism u) δ)
  have hΔ : Δ ∈ distTriang _ := T.map_distinguished _ hδ
  intro j hj
  have hz : IsZero ((homologyFunctor B j).obj (T.obj (∏ᶜ X))) := by
    let F := T ⋙ homologyFunctor B j
    let hP := isLimitFanMkObjOfIsLimit F X (Pi.π X) (productIsProduct X)
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Fan.IsLimit.hom_ext hP
    intro n
    exact (isZero_of_isLE (T.obj (X n)) (b + c) j hj).eq_of_tgt _ _
  have hepi : Epi ((homologyFunctor B (j - 1)).map Δ.mor₂) :=
    epi_map_towerTransitionEndomorphism (T ⋙ homologyFunctor B (j - 1)) u (hstable (j - 1))
  have hzeroδ : HomologySequence.δ Δ (j - 1) j (by omega) = 0 :=
    (HomologySequence.epi_homologyMap_mor₂_iff Δ hΔ (j - 1) j (by omega)).mp hepi
  exact (HomologySequence.exact₁ Δ hΔ (j - 1) j (by omega)).isZero_X₂ hzeroδ
    (hz.eq_of_tgt _ _)

end DerivedCategory
