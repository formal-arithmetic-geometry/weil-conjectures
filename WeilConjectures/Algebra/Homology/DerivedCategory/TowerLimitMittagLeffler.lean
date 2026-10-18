/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitHomology
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# `lim¹` of Mittag-Leffler towers and the Milnor sequence

For a tower `G : ℕᵒᵖ ⥤ C` in a preadditive category with a product `∏ Gₙ` and its transition
endomorphism `t` (components `∏ Gₙ ⟶ Gₙ₊₁ ⟶ Gₙ`):

- `CategoryTheory.Limits.epi_one_sub_of_essentiallyZero`: if `G` is essentially zero (for
  every `n` some transition `G m ⟶ G n` vanishes), `1 - t` is a split epimorphism, a section
  being the geometric series `∑ₖ tᵏ`, whose components are finite sums
  (`CategoryTheory.Limits.towerPartialSum`);
- `CategoryTheory.Limits.epi_one_sub_of_shortExact`: in an abelian category with exact
  countable products in which sequential limits of epimorphisms project epimorphically onto the
  first term (a replete topos), if `G` is an extension of an essentially zero tower by a tower
  with epimorphic transitions — the Mittag-Leffler condition — then `1 - t` is an
  epimorphism, i.e. `lim¹ G = 0`;
- `DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfMittagLeffler`: hence
  `Hⁱ(R lim F) = lim Hⁱ(Fₙ)` when the tower `H^{i-1}(Fₙ)` is Mittag-Leffler in this sense.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] {G : ℕᵒᵖ ⥤ C}
  {P : Fan fun n : ℕ ↦ G.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
  (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ G.map (homOfLE n.le_succ).op)

/-- The partial sums `∑_{k < K} pₙ₊ₖ ≫ G(n + k ⟶ n)`. -/
noncomputable def towerPartialSum (n K : ℕ) : P.pt ⟶ G.obj (op n) :=
  ∑ k ∈ Finset.range K, P.proj (n + k) ≫ G.map (homOfLE (n.le_add_right k)).op


omit [Preadditive C] in
lemma proj_comp_map_congr {n a b : ℕ} (h : a = b) (hn : n ≤ a) :
    P.proj a ≫ G.map (homOfLE hn).op = P.proj b ≫ G.map (homOfLE (h ▸ hn)).op := by
  subst h
  rfl

lemma towerPartialSum_succ (n K : ℕ) :
    towerPartialSum (P := P) n (K + 1) =
      P.proj n + towerPartialSum (P := P) (n + 1) K ≫ G.map (homOfLE n.le_succ).op := by
  rw [towerPartialSum, Finset.sum_range_succ', towerPartialSum, Preadditive.sum_comp,
    add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [assoc, ← G.map_comp, ← op_comp, proj_comp_map_congr (P := P) (show n + (k + 1) = n + 1 + k
      by lia)]
    rfl
/-- If the tower is essentially zero beyond `m`, the partial sums stabilise. -/
lemma towerPartialSum_eq_of_le {n m : ℕ} (hnm : n ≤ m)
    (hm : G.map (homOfLE hnm).op = 0) {K K' : ℕ} (hK : m ≤ n + K) (hK' : K ≤ K') :
    towerPartialSum (P := P) n K' = towerPartialSum (P := P) n K := by
  rw [towerPartialSum, towerPartialSum, ← Finset.sum_range_add_sum_Ico _ hK',
    add_eq_left]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hk' : m ≤ n + k := hK.trans (by have := (Finset.mem_Ico.1 hk).1; lia)
  have : homOfLE (n.le_add_right k) = homOfLE hnm ≫ homOfLE hk' := Subsingleton.elim _ _
  rw [this, op_comp, G.map_comp, hm, comp_zero, comp_zero]

include hP ht in
/-- **`lim¹` of an essentially zero tower vanishes**: if for every `n` some transition
`G m ⟶ G n` is zero, then `1 - t : ∏ Gₙ ⟶ ∏ Gₙ` is a split epimorphism, with section the
"geometric series" `∑ₖ tᵏ`, whose components are finite sums. -/
lemma epi_one_sub_of_essentiallyZero
    (hG : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), G.map (homOfLE h).op = 0) : Epi (𝟙 P.pt - t) := by
  choose m hnm hm using hG
  let s : P.pt ⟶ P.pt := Fan.IsLimit.lift hP fun n ↦ towerPartialSum (P := P) n (m n - n)
  have hs : s ≫ (𝟙 P.pt - t) = 𝟙 _ := by
    refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
    let K := max (m n - n) (m (n + 1) - (n + 1))
    rw [Preadditive.comp_sub, comp_id, Preadditive.sub_comp, assoc, ht, Fan.IsLimit.fac,
      ← assoc, Fan.IsLimit.fac, id_comp,
      ← towerPartialSum_eq_of_le (hnm n) (hm n) (K' := K + 1) (by lia) (by lia),
      ← towerPartialSum_eq_of_le (hnm (n + 1)) (hm (n + 1)) (K' := K) (by lia) (by lia),
      towerPartialSum_succ, add_sub_cancel_right]
  exact (IsSplitEpi.mk' ⟨s, hs⟩).epi

include hP ht in
/-- `1 - t` is an epimorphism on one product of a tower as soon as it is on another. -/
lemma epi_one_sub_of_isLimit {Q : Fan fun n : ℕ ↦ G.obj (op n)} (hQ : IsLimit Q) (t' : Q.pt ⟶ Q.pt)
    (ht' : ∀ n : ℕ, t' ≫ Q.proj n = Q.proj (n + 1) ≫ G.map (homOfLE n.le_succ).op)
    (h : Epi (𝟙 Q.pt - t')) : Epi (𝟙 P.pt - t) := by
  let e := hQ.conePointUniqueUpToIso hP
  have he (n : ℕ) : e.hom ≫ P.proj n = Q.proj n := hQ.conePointUniqueUpToIso_hom_comp hP ⟨n⟩
  have hc : e.hom ≫ (𝟙 P.pt - t) = (𝟙 Q.pt - t') ≫ e.hom :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      simp only [Preadditive.comp_sub, Preadditive.sub_comp, comp_id, id_comp, assoc, he, ht,
        ht', reassoc_of% he]
  have : Epi (e.hom ≫ (𝟙 P.pt - t)) := by rw [hc]; infer_instance
  exact epi_of_epi e.hom _

section Abelian

variable {C : Type*} [Category* C] [Abelian C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C]

/-- The transition endomorphism of the product `∏ Gₙ` of a tower. -/
noncomputable abbrev piTowerShift (G : ℕᵒᵖ ⥤ C) :
    ∏ᶜ (fun n : ℕ ↦ G.obj (op n)) ⟶ ∏ᶜ (fun n : ℕ ↦ G.obj (op n)) :=
  Pi.lift fun n ↦ Pi.π _ (n + 1) ≫ G.map (homOfLE n.le_succ).op

/-- **`lim¹` vanishes for Mittag-Leffler towers in a replete abelian category.** Let
`0 ⟶ G' ⟶ G ⟶ G'' ⟶ 0` be a pointwise short exact sequence of towers, where `G'` has
epimorphic transitions and `G''` is essentially zero (for instance `G'` the tower of stable
images of a Mittag-Leffler tower `G`). Then `1 - t` is an epimorphism on `∏ Gₙ`. -/
lemma epi_one_sub_of_shortExact (hC : EpiπAppZeroOfEpi C) {G' G G'' : ℕᵒᵖ ⥤ C}
    (ι : G' ⟶ G) (π : G ⟶ G'') (hιπ : ∀ n : ℕ, ι.app (op n) ≫ π.app (op n) = 0)
    (hS : ∀ n : ℕ, (ShortComplex.mk _ _ (hιπ n)).ShortExact)
    (h' : ∀ n : ℕ, Epi (G'.map (homOfLE n.le_succ).op))
    (h'' : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), G''.map (homOfLE h).op = 0)
    {P : Fan fun n : ℕ ↦ G.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ G.map (homOfLE n.le_succ).op) :
    Epi (𝟙 P.pt - t) := by
  -- the short exact sequence of products
  let SF : ShortComplex (Discrete ℕ ⥤ C) :=
    ShortComplex.mk
      (Discrete.natTrans (F := Discrete.functor fun n ↦ G'.obj (op n))
        (G := Discrete.functor fun n ↦ G.obj (op n)) fun n ↦ ι.app (op n.as))
      (Discrete.natTrans (F := Discrete.functor fun n ↦ G.obj (op n))
        (G := Discrete.functor fun n ↦ G''.obj (op n)) fun n ↦ π.app (op n.as))
      (by ext n; exact hιπ n.as)
  have hSF : SF.ShortExact := by
    have : ∀ n : Discrete ℕ, Mono (SF.f.app n) := fun n ↦ (hS n.as).mono_f
    have : ∀ n : Discrete ℕ, Epi (SF.g.app n) := fun n ↦ (hS n.as).epi_g
    refine ShortComplex.ShortExact.mk' ?_ (NatTrans.mono_of_mono_app _)
      (NatTrans.epi_of_epi_app _)
    rw [ShortComplex.exact_iff_evaluation]
    exact fun n ↦ (hS n.as).exact
  have hSP := hSF.map_of_exact (lim : (Discrete ℕ ⥤ C) ⥤ C)
  let ht₀ (H : ℕᵒᵖ ⥤ C) (n : ℕ) : piTowerShift H ≫ Pi.π _ n =
      Pi.π _ (n + 1) ≫ H.map (homOfLE n.le_succ).op := Pi.lift_π _ _
  have e' : Epi (𝟙 _ - piTowerShift G') :=
    epi_one_sub_of_epiπAppZeroOfEpi hC (productIsProduct _) _ (ht₀ G') h'
  have e'' : Epi (𝟙 _ - piTowerShift G'') :=
    epi_one_sub_of_essentiallyZero (productIsProduct _) _ (ht₀ G'') h''
  let φ : SF.map lim ⟶ SF.map lim :=
    { τ₁ := 𝟙 _ - piTowerShift G'
      τ₂ := 𝟙 _ - piTowerShift G
      τ₃ := 𝟙 _ - piTowerShift G''
      comm₁₂ := by
        refine Pi.hom_ext _ _ fun n ↦ ?_
        change ((𝟙 _ - piTowerShift G') ≫ Pi.map fun n ↦ ι.app (op n)) ≫ Pi.π _ n =
          ((Pi.map fun n ↦ ι.app (op n)) ≫ (𝟙 _ - piTowerShift G)) ≫ Pi.π _ n
        simp only [assoc, Pi.map_π, Preadditive.sub_comp, Preadditive.comp_sub, id_comp,
          comp_id, Pi.lift_π_assoc, Pi.lift_π, Pi.map_π_assoc, NatTrans.naturality]
      comm₂₃ := by
        refine Pi.hom_ext _ _ fun n ↦ ?_
        change ((𝟙 _ - piTowerShift G) ≫ Pi.map fun n ↦ π.app (op n)) ≫ Pi.π _ n =
          ((Pi.map fun n ↦ π.app (op n)) ≫ (𝟙 _ - piTowerShift G'')) ≫ Pi.π _ n
        simp only [assoc, Pi.map_π, Preadditive.sub_comp, Preadditive.comp_sub, id_comp,
          comp_id, Pi.lift_π_assoc, Pi.lift_π, Pi.map_π_assoc, NatTrans.naturality] }
  have : Epi (SF.map lim).g := hSP.epi_g
  have : Epi φ.τ₁ := e'
  have : Epi φ.τ₃ := e''
  have : Epi (𝟙 _ - piTowerShift G) := ShortComplex.epi_τ₂_of_exact_of_epi φ hSP.exact
  exact epi_one_sub_of_isLimit hP t ht (productIsProduct _) _ (ht₀ G) this

end Abelian

end CategoryTheory.Limits

namespace DerivedCategory

open Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C]
  {F : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone F}

/-- **The Milnor sequence for Mittag-Leffler towers**: in an abelian category with exact
countable products in which sequential limits of epimorphisms project epimorphically onto the
first term, let `c` be a homotopy limit cone over a tower `F` in `D(C)` whose cohomology tower
`H^{i-1}(Fₙ)` is an extension of an essentially zero tower `G''` by a tower `G'` with
epimorphic transitions (the Mittag-Leffler condition, `G'` being the stable images). Then
`Hⁱ(R lim F) = lim Hⁱ(Fₙ)`. -/
noncomputable def isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfMittagLeffler
    (hC : EpiπAppZeroOfEpi C) (hc : IsHomotopyLimit c) (i : ℤ) {G' G'' : ℕᵒᵖ ⥤ C}
    (ι : G' ⟶ F ⋙ homologyFunctor C (i - 1)) (π : F ⋙ homologyFunctor C (i - 1) ⟶ G'')
    (hιπ : ∀ n : ℕ, ι.app (op n) ≫ π.app (op n) = 0)
    (hS : ∀ n : ℕ, (ShortComplex.mk _ _ (hιπ n)).ShortExact)
    (h' : ∀ n : ℕ, Epi (G'.map (homOfLE n.le_succ).op))
    (h'' : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), G''.map (homOfLE h).op = 0) :
    IsLimit ((homologyFunctor C i).mapCone c) :=
  isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfEpi hc i fun hQ t ht ↦
    CategoryTheory.Limits.epi_one_sub_of_shortExact hC ι π hιπ hS h' h'' hQ t ht

end DerivedCategory
