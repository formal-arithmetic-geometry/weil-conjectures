/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# `Spec` of a restriction map and the canonical isomorphisms of affine opens

We record that `Spec` of a restriction map between affine opens intertwines the canonical
isomorphisms `Spec Γ(X, U) ≅ U` with the inclusion of opens, and that the algebra map
realizing `Γ(X, X.basicOpen f)` as a localization is the restriction map of the structure
sheaf.

We also record that an open of an affine scheme is covered by finitely many basic opens
as soon as it is quasi-compact (`AlgebraicGeometry.exists_finite_basicOpen_cover`), and
that over such a cover a finite family of sections admits a common denominator with exact
transition identities (`AlgebraicGeometry.exists_common_denominator_of_isCompact`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The `Spec` of a restriction map intertwines the canonical isomorphisms
`Spec Γ(X, U) ≅ U` with the inclusion of opens. -/
lemma specMap_res_isoSpec_inv {U V : X.affineOpens} (hUV : U ≤ V) :
    Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hUV).op) ≫ V.2.isoSpec.inv =
      U.2.isoSpec.inv ≫ X.homOfLE hUV := by
  rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι,
    V.2.map_fromSpec U.2 (homOfLE (X := X.Opens) hUV).op]

/-- The algebra map exhibiting the sections over a basic open as a localization is the
restriction map of the structure sheaf. -/
lemma algebraMap_basicOpen_eq {U : X.Opens} (f : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom :=
  rfl

/-- A quasi-compact open of an affine scheme is a finite union of basic opens. -/
lemma exists_finite_basicOpen_cover [IsAffine X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (u : ι → Γ(X, ⊤)) (_ : ∀ i, X.basicOpen (u i) ≤ U),
      U = ⨆ i, X.basicOpen (u i) := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun a : {a : Γ(X, ⊤) // X.basicOpen a ≤ U} ↦ (X.basicOpen a.1 : Set X))
    (fun a ↦ (X.basicOpen a.1).2) (by
      intro x hx
      obtain ⟨a, ha1, ha2⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := U) ⟨x, hx⟩ trivial
      exact Set.mem_iUnion.mpr ⟨⟨a, ha1⟩, ha2⟩)
  refine ⟨{a : {a : Γ(X, ⊤) // X.basicOpen a ≤ U} // a ∈ t}, inferInstance,
    fun a ↦ a.1.1, fun a ↦ a.1.2, le_antisymm ?_ (iSup_le fun a ↦ a.1.2)⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩

/-- **Common denominators on a quasi-compact open of an affine scheme.** A finite family
`s` of sections over a quasi-compact open `U` of an affine scheme `X` is, over a finite
cover of `U` by basic opens `D(uᵢ)`, given by fractions `cᵢⱼ / uᵢ ^ N` for a single
exponent `N`, and the numerators can be chosen so that the compatibilities
`cᵢⱼ · uᵢ'^N = cᵢ'ⱼ · uᵢ^N` hold *exactly* in `Γ(X, ⊤)`. -/
lemma exists_common_denominator_of_isCompact {X : Scheme.{u}} [IsAffine X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) {σ : Type u} [Finite σ] (s : σ → Γ(U.toScheme, ⊤)) :
    ∃ (ι : Type u) (_ : Finite ι) (u : ι → Γ(X, ⊤)) (hle : ∀ i, X.basicOpen (u i) ≤ U)
      (N : ℕ) (c : ι → σ → Γ(X, ⊤)),
      U = ⨆ i, X.basicOpen (u i) ∧ 0 < N ∧
      (∀ i i' j, c i j * u i' ^ N = c i' j * u i ^ N) ∧
      (∀ i j, (X.homOfLE (hle i)).appTop (s j) *
          (X.basicOpen (u i)).ι.appTop (u i ^ N) = (X.basicOpen (u i)).ι.appTop (c i j)) := by
  classical
  obtain ⟨ι, hι, u, hle, hUeq⟩ := exists_finite_basicOpen_cover hU
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype σ := Fintype.ofFinite σ
  set t : ∀ i : ι, σ → Γ((X.basicOpen (u i)).toScheme, ⊤) :=
    fun i j ↦ (X.homOfLE (hle i)).appTop (s j) with ht
  -- the coordinates are fractions with a power of `u i` as denominator
  have hfrac : ∀ i j, ∃ (a : Γ(X, ⊤)) (k : ℕ),
      t i j * (X.basicOpen (u i)).ι.appTop (u i ^ k) =
        (X.basicOpen (u i)).ι.appTop a := by
    intro i j
    obtain ⟨⟨num, den⟩, hfrac⟩ := IsLocalization.surj (Submonoid.powers (u i)) (t i j)
    obtain ⟨k, hk⟩ := den.2
    have hk' : u i ^ k = (den : Γ(X, ⊤)) := hk
    exact ⟨num, k, by rw [hk']; exact hfrac⟩
  choose a k hak using hfrac
  -- one exponent works for all coordinates
  set N : ℕ := Finset.univ.sup fun p : ι × σ ↦ k p.1 p.2
  have hkN : ∀ i j, k i j ≤ N := fun i j ↦ Finset.le_sup (f := fun p : ι × σ ↦ k p.1 p.2)
    (Finset.mem_univ (i, j))
  have hfrac2 : ∀ i j, ∃ num : Γ(X, ⊤),
      t i j * (X.basicOpen (u i)).ι.appTop (u i ^ N) = (X.basicOpen (u i)).ι.appTop num := by
    intro i j
    refine ⟨a i j * u i ^ (N - k i j), ?_⟩
    have hpow : u i ^ N = u i ^ k i j * u i ^ (N - k i j) := by
      rw [← pow_add, Nat.add_sub_cancel' (hkN i j)]
    rw [hpow, map_mul, map_mul, ← mul_assoc, hak i j]
  choose b hbN using hfrac2
  -- the numerators agree on the overlaps after multiplying by a power of the denominators
  have hover : ∀ i i' j, ∃ m : ℕ,
      (u i * u i') ^ m * (b i j * u i' ^ N - b i' j * u i ^ N) = 0 := by
    intro i i' j
    have hii' : X.basicOpen (u i * u i') ≤ X.basicOpen (u i) := by
      rw [Scheme.basicOpen_mul]; exact inf_le_left
    have hi'i : X.basicOpen (u i * u i') ≤ X.basicOpen (u i') := by
      rw [Scheme.basicOpen_mul]; exact inf_le_right
    -- the two local coordinates restrict to the same section on the overlap
    have hres : ∀ (i₀ : ι) (h : X.basicOpen (u i * u i') ≤ X.basicOpen (u i₀))
        (x : Γ(X, ⊤)), (X.homOfLE h).appTop ((X.basicOpen (u i₀)).ι.appTop x) =
          (X.basicOpen (u i * u i')).ι.appTop x := by
      intro i₀ h x
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]
    have hcommon : (X.homOfLE hii').appTop (t i j) = (X.homOfLE hi'i).appTop (t i' j) := by
      simp only [ht]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE, Scheme.homOfLE_homOfLE]
    have h1 := congrArg (X.homOfLE hii').appTop (hbN i j)
    have h2 := congrArg (X.homOfLE hi'i).appTop (hbN i' j)
    rw [map_mul, hres i hii', hres i hii'] at h1
    rw [map_mul, hres i' hi'i, hres i' hi'i, ← hcommon] at h2
    have h3 : (X.basicOpen (u i * u i')).ι.appTop (b i j * u i' ^ N) =
        (X.basicOpen (u i * u i')).ι.appTop (b i' j * u i ^ N) := by
      rw [map_mul, map_mul, ← h1, ← h2]; ring
    obtain ⟨ann, hann⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers (u i * u i')) (S := Γ((X.basicOpen (u i * u i')).toScheme, ⊤)) h3
    obtain ⟨e, he⟩ := ann.2
    have he' : (u i * u i') ^ e = (ann : Γ(X, ⊤)) := he
    exact ⟨e, by rw [he', mul_sub, hann, sub_self]⟩
  choose m hm using hover
  set M : ℕ := Finset.univ.sup (fun p : ι × ι × σ ↦ m p.1 p.2.1 p.2.2) + 1
  have hmM : ∀ i i' j, m i i' j ≤ M := fun i i' j ↦
    (Finset.le_sup (f := fun p : ι × ι × σ ↦ m p.1 p.2.1 p.2.2)
      (Finset.mem_univ (i, i', j))).trans (Nat.le_succ _)
  have hmM' : ∀ i i' j, (u i * u i') ^ M * (b i j * u i' ^ N - b i' j * u i ^ N) = 0 := by
    intro i i' j
    have : (u i * u i') ^ M = (u i * u i') ^ (M - m i i' j) * (u i * u i') ^ m i i' j := by
      rw [← pow_add, Nat.sub_add_cancel (hmM i i' j)]
    rw [this, mul_assoc, hm i i' j, mul_zero]
  refine ⟨ι, inferInstance, u, hle, N + M, fun i j ↦ b i j * u i ^ M, hUeq,
    by omega, ?_, ?_⟩
  · intro i i' j
    have := hmM' i i' j
    rw [mul_pow, mul_sub, sub_eq_zero] at this
    calc b i j * u i ^ M * u i' ^ (N + M)
        = u i ^ M * u i' ^ M * (b i j * u i' ^ N) := by ring
      _ = u i ^ M * u i' ^ M * (b i' j * u i ^ N) := this
      _ = b i' j * u i' ^ M * u i ^ (N + M) := by ring
  · intro i j
    rw [pow_add, map_mul, ← mul_assoc, hbN i j, ← map_mul]

end AlgebraicGeometry
