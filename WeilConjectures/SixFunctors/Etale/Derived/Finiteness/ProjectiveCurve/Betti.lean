/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.Curve.ExtensionInvariance
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.CurvePairing
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Betti numbers of smooth proper curves over an algebraically closed field

Let `Y` be a smooth proper scheme of relative dimension one over an algebraically closed field
`K`, and `ℓ` a prime invertible in `K`. Its finitely many connected components are smooth
proper connected curves, so the curve estimate (`thm-sc-proper-cohomology`) gives
`|H⁰(Y, ℤ/ℓ)| = |H²(Y, ℤ/ℓ)| = ℓ^c` and `|H¹(Y, ℤ/ℓ)| = ℓ^{2g}`, where `c` is the number of
connected components of `Y` and `g = dim H¹(Y, 𝒪_Y)` its arithmetic genus, the sum of the genera
of the components (`AlgebraicGeometry.natCard_sheafH_constantZMod_of_smoothOfRelativeDimension`).
Moreover `c = dim H⁰(Y, 𝒪_Y)`
(`AlgebraicGeometry.finrankH_unit_zero_eq_natCard_connectedComponents`). This is the fibrewise part
of `lem-fin-projective-curve-betti-cardinalities`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- The connected components of a scheme with Noetherian underlying space form a finite
decomposition into nonempty connected open and closed subsets. -/
lemma exists_opens_connectedComponents (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y] :
    ∃ U : _root_.ConnectedComponents Y → Y.Opens, (∀ c, IsClosed (U c : Set Y)) ∧
      Pairwise (fun c d ↦ Disjoint (U c : Set Y) (U d)) ∧ (∀ y : Y, ∃ c, y ∈ U c) ∧
      ∀ c, ConnectedSpace (U c) ∧ Nonempty (U c) := by
  refine ⟨fun c ↦ ⟨ConnectedComponents.mk ⁻¹' {c}, ?_⟩, fun c ↦ ?_, fun c d hcd ↦ ?_,
    fun y ↦ ⟨ConnectedComponents.mk y, Set.mem_singleton _⟩,
    fun c ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact TopologicalSpace.NoetherianSpace.isOpen_connectedComponent x
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    change IsClosed (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
    rw [connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent
  · exact Set.disjoint_left.2 fun y hc hd ↦ hcd ((Set.mem_singleton_iff.1 hc).symm.trans hd)
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    have h : (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x} : Set Y) =
        connectedComponent x :=
      connectedComponents_preimage_singleton
    refine ⟨?_, ⟨x, ?_⟩⟩
    · change ConnectedSpace (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x} : Set Y)
      rw [h]
      exact isConnected_iff_connectedSpace.1 isConnected_connectedComponent
    · change x ∈ (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x} : Set Y)
      rw [h]
      exact mem_connectedComponent

/-- A family of open subsets of a scheme which are pairwise disjoint and cover it is pairwise
disjoint and has supremum `⊤` as a family of opens. -/
lemma pairwise_disjoint_and_iSup_eq_top {Y : Scheme.{u}} {ι : Type*} (U : ι → Y.Opens)
    (hUd : Pairwise (fun c d ↦ Disjoint (U c : Set Y) (U d))) (hUcov : ∀ y : Y, ∃ c, y ∈ U c) :
    Pairwise (Function.onFun Disjoint U) ∧ ⨆ c, U c = ⊤ := by
  refine ⟨fun c d hcd ↦ ?_, eq_top_iff.2 fun y _ ↦ ?_⟩
  · rw [Function.onFun, disjoint_iff]
    ext x
    simpa using fun h₁ h₂ ↦ Set.disjoint_left.1 (hUd hcd) h₁ h₂
  · obtain ⟨c, hc⟩ := hUcov y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, hc⟩

section Fibre

variable {K : Type u} [Field K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of K))] [IsProper (Y ↘ Spec (.of K))]

/-- A connected open and closed subscheme `U` of a smooth proper scheme `Y` of relative dimension
one over `K` is smooth and proper of relative dimension one over `K`. -/
lemma smoothOfRelativeDimension_isProper_of_isClosed (U : Y.Opens) (hU : IsClosed (U : Set Y)) :
    letI : U.toScheme.Over (Spec (.of K)) := ⟨U.ι ≫ Y ↘ Spec (.of K)⟩
    SmoothOfRelativeDimension 1 (U.toScheme ↘ Spec (.of K)) ∧
      IsProper (U.toScheme ↘ Spec (.of K)) := by
  let : U.toScheme.Over (Spec (.of K)) := ⟨U.ι ≫ Y ↘ Spec (.of K)⟩
  have : IsClosedImmersion U.ι := .of_isOpenImmersion _ (by simpa using hU)
  exact ⟨inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ Y ↘ Spec (.of K))),
    inferInstanceAs (IsProper (U.ι ≫ Y ↘ Spec (.of K)))⟩

omit [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of K))] in
/-- **Arithmetic genus of a disjoint union.** If `Y` is the disjoint union of finitely many open
and closed subschemes `U c`, its arithmetic genus is the sum of theirs. -/
lemma arithmeticGenus_eq_sum {ι : Type u} [Fintype ι] (U : ι → Y.Opens)
    (hUd : Pairwise (fun c d ↦ Disjoint (U c : Set Y) (U d))) (hUcov : ∀ y : Y, ∃ c, y ∈ U c) :
    arithmeticGenus K Y = ∑ c,
      let : (U c).toScheme.Over (Spec (.of K)) := ⟨(U c).ι ≫ Y ↘ Spec (.of K)⟩
      arithmeticGenus K (U c).toScheme := by
  have : (SheafOfModules.unit Y.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have := Modules.finiteDimensional_H_of_isProper (k := K) (SheafOfModules.unit Y.ringCatSheaf) 1
  obtain ⟨hdisj, hcover⟩ := pairwise_disjoint_and_iSup_eq_top U hUd hUcov
  refine (Modules.finrankH_eq_sum_of_pairwise_disjoint K U hdisj hcover _ 1).trans
    (Finset.sum_congr rfl fun c _ ↦ ?_)
  let : (U c).toScheme.Over (Spec (.of K)) := ⟨(U c).ι ≫ Y ↘ Spec (.of K)⟩
  exact Modules.finrankH_congr K (Modules.pullbackObjUnitIso (U c).ι) 1

variable [IsAlgClosed K]

/-- **Global functions on a smooth proper curve.** If `Y` is smooth and proper of relative
dimension one over an algebraically closed field `K`, then `dim_K H⁰(Y, 𝒪_Y)` is the number of
connected components of `Y`: each of them has `K` as its ring of global functions. -/
theorem finrankH_unit_zero_eq_natCard_connectedComponents :
    Modules.finrankH K (SheafOfModules.unit Y.ringCatSheaf) 0 =
      Nat.card (_root_.ConnectedComponents Y) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of K))
  have : IsNoetherian Y := {}
  obtain ⟨U, hUc, hUd, hUcov, hUconn⟩ := exists_opens_connectedComponents Y
  have := Fintype.ofFinite (_root_.ConnectedComponents Y)
  have : (SheafOfModules.unit Y.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have := Modules.finiteDimensional_H_of_isProper (k := K) (SheafOfModules.unit Y.ringCatSheaf) 0
  obtain ⟨hdisj, hcover⟩ := pairwise_disjoint_and_iSup_eq_top U hUd hUcov
  rw [Modules.finrankH_eq_sum_of_pairwise_disjoint K U hdisj hcover _ 0,
    Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  let : (U c).toScheme.Over (Spec (.of K)) := ⟨(U c).ι ≫ Y ↘ Spec (.of K)⟩
  obtain ⟨_, _⟩ := smoothOfRelativeDimension_isProper_of_isClosed (K := K) Y (U c) (hUc c)
  have := (hUconn c).1
  have : Smooth ((U c).toScheme ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have : GlobalSectionsBijective K (U c).toScheme := GlobalSectionsBijective.of_isSepClosed (k := K)
  exact (Modules.finrankH_congr K (Modules.pullbackObjUnitIso (U c).ι) 0).trans
    (Modules.finrankH_unit_zero (k := K) (X := (U c).toScheme))

/-- **Betti numbers of a smooth proper curve.** Let `Y` be smooth and proper of relative
dimension one over an algebraically closed field `K`, with `c` connected components and
arithmetic genus `g`, and let `ℓ` be a prime invertible in `K`. Then `|H⁰(Y, ℤ/ℓ)| = ℓ^c`,
`|H¹(Y, ℤ/ℓ)| = ℓ^{2g}`, `|H²(Y, ℤ/ℓ)| = ℓ^c` and `|Hʳ(Y, ℤ/ℓ)| = 1` for `r > 2`: the cohomology
of `Y` is the product of that of its components, which are smooth proper connected curves, and
the genus of `Y` is the sum of their genera. -/
theorem natCard_sheafH_constantZMod_of_smoothOfRelativeDimension (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) :
    Nat.card (Sheaf.H (Y.constantZMod ℓ) 0) = ℓ ^ Nat.card (_root_.ConnectedComponents Y) ∧
      Nat.card (Sheaf.H (Y.constantZMod ℓ) 1) = ℓ ^ (2 * arithmeticGenus K Y) ∧
      Nat.card (Sheaf.H (Y.constantZMod ℓ) 2) = ℓ ^ Nat.card (_root_.ConnectedComponents Y) ∧
      ∀ r, 2 < r → Nat.card (Sheaf.H (Y.constantZMod ℓ) r) = 1 := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of K))
  have : IsNoetherian Y := {}
  obtain ⟨U, hUc, hUd, hUcov, hUconn⟩ := exists_opens_connectedComponents Y
  have := Fintype.ofFinite (_root_.ConnectedComponents Y)
  -- the cohomology of `Y` is the product of that of its connected components
  have hH (n : ℕ) : Nat.card (Sheaf.H (Y.constantZMod ℓ) n) =
      ∏ c, Nat.card (Sheaf.H ((U c).toScheme.constantZMod ℓ) n) := by
    obtain ⟨e⟩ := Etale.nonempty_equiv_pi_H_of_isClopen U hUc hUd hUcov (Y.constantZMod ℓ) n
    rw [Nat.card_congr e, Nat.card_pi]
    exact Finset.prod_congr rfl fun c _ ↦
      Nat.card_congr ((U c).ι.sheafHUpperStarConstantZModAddEquiv ℓ n).toEquiv
  -- each component is a smooth proper connected curve
  have hC (c : _root_.ConnectedComponents Y) :
      let : (U c).toScheme.Over (Spec (.of K)) := ⟨(U c).ι ≫ Y ↘ Spec (.of K)⟩
      Nat.card (Sheaf.H ((U c).toScheme.constantZMod ℓ) 0) = ℓ ∧
        Nat.card (Sheaf.H ((U c).toScheme.constantZMod ℓ) 1) =
          ℓ ^ (2 * arithmeticGenus K (U c).toScheme) ∧
        Nat.card (Sheaf.H ((U c).toScheme.constantZMod ℓ) 2) = ℓ ∧
        ∀ r, 2 < r → Nat.card (Sheaf.H ((U c).toScheme.constantZMod ℓ) r) = 1 := by
    let : (U c).toScheme.Over (Spec (.of K)) := ⟨(U c).ι ≫ Y ↘ Spec (.of K)⟩
    obtain ⟨_, _⟩ := smoothOfRelativeDimension_isProper_of_isClosed (K := K) Y (U c) (hUc c)
    obtain ⟨_, _⟩ := hUconn c
    have : IsConnectedCurve ((U c).toScheme ↘ Spec (.of K)) :=
      Scheme.EtaleTorsor.isConnectedCurve (k := K) (X := (U c).toScheme)
    have : Smooth ((U c).toScheme ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 1 _
    obtain ⟨⟨e₀⟩, ⟨e₁⟩, ⟨e₂⟩, h₃⟩ :=
      IsConnectedCurve.sheafH_constantZMod_of_isProper ((U c).toScheme ↘ Spec (.of K)) ℓ hℓ
    refine ⟨?_, ?_, ?_, fun r hr ↦ ?_⟩
    · rw [Nat.card_congr e₀.toEquiv, Nat.card_zmod]
    · rw [Nat.card_congr e₁.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
        Fintype.card_fin, genus_eq_arithmeticGenus]
    · rw [Nat.card_congr e₂.toEquiv, Nat.card_zmod]
    · have := h₃ r hr
      exact Nat.card_of_subsingleton (0 : Sheaf.H ((U c).toScheme.constantZMod ℓ) r)
  refine ⟨?_, ?_, ?_, fun r hr ↦ ?_⟩
  · rw [hH, Finset.prod_congr rfl fun c _ ↦ (hC c).1, Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  · rw [hH, Finset.prod_congr rfl fun c _ ↦ (hC c).2.1, Finset.prod_pow_eq_pow_sum,
      ← Finset.mul_sum, ← arithmeticGenus_eq_sum (K := K) Y U hUd hUcov]
  · rw [hH, Finset.prod_congr rfl fun c _ ↦ (hC c).2.2.1, Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  · rw [hH, Finset.prod_congr rfl fun c _ ↦ (hC c).2.2.2 r hr, Finset.prod_const_one]

end Fibre

end AlgebraicGeometry
