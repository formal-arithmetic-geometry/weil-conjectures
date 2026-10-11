/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.AlgebraicGeometry.Cohomology.PushforwardZero
public import WeilConjectures.Mathlib.Algebra.Homology.HomologySequence

/-!
# Cohomology computed by acyclic resolutions

Let `K` be a cochain complex of `𝒪_X`-modules, exact in positive degrees, whose terms have
vanishing cohomology in positive degrees, and let `Zᵏ` be its cycles. The short exact sequences
`0 ⟶ Zᵏ ⟶ Kᵏ ⟶ Zᵏ⁺¹ ⟶ 0` give, by dimension shifting, isomorphisms
`H^{n+1}(X, Z⁰) ≅ H¹(X, Zⁿ) ≅ Γ(X, Zⁿ⁺¹) / Γ(X, Kⁿ)`; for a resolution `K` of `M` this computes
`H^{n+1}(X, M)` as the cohomology of the complex of global sections `Γ(X, K)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.H.δ_naturality`: the connecting map is natural.
- `AlgebraicGeometry.Scheme.Modules.H.bijective_δ_of_subsingleton`: the connecting map of a short
  exact sequence whose middle term is acyclic is bijective in positive degrees.
- `AlgebraicGeometry.Scheme.Modules.H.cyclesShiftAddEquiv`: `H^{m+1}(X, Zᵏ) ≅ H¹(X, Zᵏ⁺ᵐ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Delta

variable {S S' : ShortComplex X.Modules}

/-- **Naturality of the connecting map.** For a morphism `φ : S ⟶ S'` of short exact sequences,
`δ' ∘ H^n(φ₃) = H^{n+1}(φ₁) ∘ δ`. -/
lemma H.δ_naturality (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') (n : ℕ)
    (z : S.X₃.H n) :
    H.δ hS' n (H.map φ.τ₃ n z) = H.map φ.τ₁ (n + 1) (H.δ hS n z) := by
  have h : (shortExact_map_toSheaf hS).extClass.comp (Ext.mk₀ ((toAb X).map φ.τ₁))
      (add_zero 1) =
      (Ext.mk₀ ((toAb X).map φ.τ₃)).comp (shortExact_map_toSheaf hS').extClass
      (zero_add 1) :=
    have h₁ := shortExact_map_toSheaf hS
    have h₂ := shortExact_map_toSheaf hS'
    let φ' : S.map (toAb X) ⟶ S'.map (toAb X) := (toAb X).mapShortComplex.map φ
    ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ'
  rw [H.δ_apply, H.δ_apply, H.map_apply_eq_comp, H.map_apply_eq_comp,
    Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, h]

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `H^{n+1}(M₂) = H^{n+2}(M₂) = 0`, the
connecting map `δ : H^{n+1}(M₃) ⟶ H^{n+2}(M₁)` is bijective. -/
lemma H.bijective_δ_of_subsingleton (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (S.X₂.H (n + 1))] [Subsingleton (S.X₂.H (n + 2))] :
    Function.Bijective (H.δ hS (n + 1)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨z, rfl⟩ : x ∈ (H.map S.g (n + 1)).range := by
      rw [← H.ker_δ_eq_range_map_g]; exact hx
    rw [Subsingleton.elim z 0, map_zero]
  · have : y ∈ (H.map S.f (n + 2)).ker := by
      rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _
    rw [H.ker_map_f_eq_range_δ] at this
    exact this

/-- The connecting map `δ : H^{n+1}(M₃) ≃+ H^{n+2}(M₁)` of a short exact sequence whose middle
term is acyclic in degrees `n + 1` and `n + 2`. -/
noncomputable def H.δAddEquiv (hS : S.ShortExact) (n : ℕ) [Subsingleton (S.X₂.H (n + 1))]
    [Subsingleton (S.X₂.H (n + 2))] : S.X₃.H (n + 1) ≃+ S.X₁.H (n + 2) :=
  AddEquiv.ofBijective (H.δ hS (n + 1)) (H.bijective_δ_of_subsingleton hS n)

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `H¹(M₂) = 0`, the connecting map
`δ : H⁰(M₃) ⟶ H¹(M₁)` is surjective. -/
lemma H.surjective_δ_zero (hS : S.ShortExact) [Subsingleton (S.X₂.H 1)] :
    Function.Surjective (H.δ hS 0) := fun y ↦ by
  have : y ∈ (H.map S.f (0 + 1)).ker := by
    rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _
  rw [H.ker_map_f_eq_range_δ] at this
  exact this

/-- **Left exactness of global sections.** For a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0`, the sections of `M₂` killed by `g` are those coming from `M₁`. -/
lemma range_app_f_eq_ker_app_g (hS : S.ShortExact) :
    (S.f.app ⊤).hom.range = (S.g.app ⊤).hom.ker := by
  ext s
  have h := fun x : S.X₂.H 0 ↦ SetLike.ext_iff.mp (H.ker_map_g_eq_range_map_f hS 0) x
  constructor
  · rintro ⟨t, rfl⟩
    rw [AddMonoidHom.mem_ker, ← ConcreteCategory.comp_apply, ← Hom.comp_app, S.zero]
    rfl
  · intro hs
    obtain ⟨t, ht⟩ := (h ((H.zeroLinearEquiv _).symm s)).1 (by
      rw [AddMonoidHom.mem_ker]
      refine (H.zeroLinearEquiv _).injective ?_
      rw [H.zeroLinearEquiv_map, LinearEquiv.apply_symm_apply, map_zero]
      exact hs)
    refine ⟨H.zeroLinearEquiv _ t, ?_⟩
    have := H.zeroLinearEquiv_map S.f t
    rw [ht, LinearEquiv.apply_symm_apply] at this
    exact this.symm

/-- For a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `H¹(M₁) = 0`, every global section
of `M₃` lifts to `M₂`. -/
lemma surjective_app_g_of_subsingleton (hS : S.ShortExact) [Subsingleton (S.X₁.H 1)] :
    Function.Surjective (S.g.app ⊤).hom := fun s ↦ by
  have hs : (H.zeroLinearEquiv _).symm s ∈ (H.δ hS 0).ker := by
    rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _
  rw [H.ker_δ_eq_range_map_g] at hs
  obtain ⟨t, ht⟩ := hs
  refine ⟨H.zeroLinearEquiv _ t, ?_⟩
  have := H.zeroLinearEquiv_map S.g t
  rw [ht, LinearEquiv.apply_symm_apply] at this
  exact this.symm

end Delta

/-- An isomorphism of `𝒪_X`-modules induces an additive isomorphism on cohomology. -/
noncomputable def H.mapAddEquiv {M N : X.Modules} (e : M ≅ N) (n : ℕ) : M.H n ≃+ N.H n :=
  (H.mapLinearEquiv e n).toAddEquiv

section Shift

variable (K : CochainComplex X.Modules ℕ) (hK : ∀ j, K.ExactAt (j + 1))
  (hacyc : ∀ j m, Subsingleton ((K.X j).H (m + 1)))

include hK in
/-- The short exact sequence `0 ⟶ Zᵏ ⟶ Kᵏ ⟶ Zᵏ⁺¹ ⟶ 0` of cycles of `K`. -/
lemma shortExact_cyclesShortComplex (k : ℕ) : (K.cyclesShortComplex k (k + 1)).ShortExact :=
  (hK k).shortExact_cyclesShortComplex rfl

include hK hacyc in
/-- **Dimension shifting.** For a complex `K` exact in positive degrees whose terms are acyclic,
`H^{m+1}(X, Zᵏ) ≅ H¹(X, Zᵏ⁺ᵐ)`, the inverse of a composite of connecting maps of the sequences
`0 ⟶ Zʲ ⟶ Kʲ ⟶ Zʲ⁺¹ ⟶ 0`. -/
noncomputable def H.cyclesShiftAddEquiv : ∀ (m k : ℕ), (K.cycles k).H (m + 1) ≃+
    (K.cycles (k + m)).H 1
  | 0, _ => AddEquiv.refl _
  | m + 1, k =>
    have : Subsingleton ((K.cyclesShortComplex k (k + 1)).X₂.H (m + 1)) := hacyc k m
    have : Subsingleton ((K.cyclesShortComplex k (k + 1)).X₂.H (m + 2)) := hacyc k (m + 1)
    (H.δAddEquiv (shortExact_cyclesShortComplex K hK k) m).symm.trans
      ((H.cyclesShiftAddEquiv m (k + 1)).trans
        (H.mapAddEquiv (eqToIso (by rw [Nat.add_assoc, Nat.add_comm 1 m])) 1))

include hK in
/-- The surjection `Γ(X, Zⁿ⁺¹) ⟶ H¹(X, Zⁿ)` of the sequence `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0`: the
connecting map, which is surjective as `H¹(X, Kⁿ) = 0`, with kernel the sections coming from
`Kⁿ`. -/
noncomputable def H.cyclesδZero (n : ℕ) : Γ(K.cycles (n + 1), ⊤) →+ (K.cycles n).H 1 :=
  (H.δ (shortExact_cyclesShortComplex K hK n) 0).comp
    (H.zeroLinearEquiv (K.cycles (n + 1))).symm.toAddMonoidHom

include hacyc in
lemma H.surjective_cyclesδZero (n : ℕ) : Function.Surjective (H.cyclesδZero K hK n) := by
  have : Subsingleton ((K.cyclesShortComplex n (n + 1)).X₂.H 1) := hacyc n 0
  exact (H.surjective_δ_zero (shortExact_cyclesShortComplex K hK n)).comp
    (H.zeroLinearEquiv (K.cycles (n + 1))).symm.surjective

lemma H.ker_cyclesδZero (n : ℕ) :
    (H.cyclesδZero K hK n).ker =
      ((K.toCycles n (n + 1)).app ⊤).hom.range := by
  ext s
  change H.δ (shortExact_cyclesShortComplex K hK n) 0 ((H.zeroLinearEquiv _).symm s) = 0 ↔ _
  rw [← AddMonoidHom.mem_ker, H.ker_δ_eq_range_map_g]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨H.zeroLinearEquiv _ y, ?_⟩
    have := H.zeroLinearEquiv_map (K.toCycles n (n + 1)) y
    change H.zeroLinearEquiv _ (H.map (K.cyclesShortComplex n (n + 1)).g 0 y) = _ at this
    rw [hy] at this
    simpa using this.symm
  · rintro ⟨y, rfl⟩
    refine ⟨(H.zeroLinearEquiv _).symm y, (H.zeroLinearEquiv _).injective ?_⟩
    change H.zeroLinearEquiv _ (H.map (K.toCycles n (n + 1)) 0 _) = _
    rw [H.zeroLinearEquiv_map]
    erw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- `H¹(X, Zⁿ) ≅ Γ(X, Zⁿ⁺¹) / Γ(X, Kⁿ)` for a complex `K` exact in positive degrees with
acyclic terms. -/
noncomputable def H.cyclesOneAddEquiv (n : ℕ) :
    (K.cycles n).H 1 ≃+ Γ(K.cycles (n + 1), ⊤) ⧸
      ((K.toCycles n (n + 1)).app ⊤).hom.range :=
  ((QuotientAddGroup.quotientAddEquivOfEq (H.ker_cyclesδZero K hK n)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (H.surjective_cyclesδZero K hK hacyc n))).symm

/-- **Cohomology computed by an acyclic resolution.** For a complex `K` exact in positive
degrees with acyclic terms, `H^{n+1}(X, Z⁰) ≅ Γ(X, Zⁿ⁺¹) / Γ(X, Kⁿ)`: the cohomology of `Z⁰`,
the module resolved by `K`, is the cohomology of the complex of global sections of `K`. -/
noncomputable def H.cyclesZeroSuccAddEquiv (n : ℕ) :
    (K.cycles 0).H (n + 1) ≃+ Γ(K.cycles (n + 1), ⊤) ⧸
      ((K.toCycles n (n + 1)).app ⊤).hom.range :=
  ((H.cyclesShiftAddEquiv K hK hacyc n 0).trans
    (H.mapAddEquiv (eqToIso (by rw [Nat.zero_add])) 1)).trans
    (H.cyclesOneAddEquiv K hK hacyc n)

end Shift
/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `Hⁿ(M₁) = Hⁿ(M₃) = 0`, also
`Hⁿ(M₂) = 0`. -/
lemma subsingleton_H_X₂_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (S.X₁.H n)] [Subsingleton (S.X₃.H n)] : Subsingleton (S.X₂.H n) := by
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : S.X₂.H n, z = 0 by rw [h x, h y]
  intro z
  have hz : z ∈ (H.map S.g n).ker := by rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _
  rw [H.ker_map_g_eq_range_map_f hS] at hz
  obtain ⟨w, rfl⟩ := hz
  rw [Subsingleton.elim w 0, map_zero]

section CohomologySheaves

variable (L : CochainComplex X.Modules ℕ)

/-- The short complex `Zᵠ ⟶ Lᵠ ⟶ Bᵠ⁺¹` of cycles, terms and boundaries of a complex `L`. -/
noncomputable def cyclesBoundariesShortComplex (q : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (L.iCycles q) (factorThruImage (L.toCycles q (q + 1))) (by
    rw [← cancel_mono (Limits.image.ι (L.toCycles q (q + 1))), Category.assoc, Limits.image.fac,
      ← cancel_mono (L.iCycles (q + 1)), Category.assoc, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCycles_d, zero_comp, zero_comp])

/-- The sequence `0 ⟶ Zᵠ ⟶ Lᵠ ⟶ Bᵠ⁺¹ ⟶ 0` is short exact. -/
lemma shortExact_cyclesBoundariesShortComplex (q : ℕ) :
    (cyclesBoundariesShortComplex L q).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ (inferInstanceAs (Mono (L.iCycles q)))
    (inferInstanceAs (Epi (factorThruImage _)))
  let φ : cyclesBoundariesShortComplex L q ⟶ ShortComplex.mk _ _ (L.iCycles_d q (q + 1)) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Limits.image.ι (L.toCycles q (q + 1)) ≫ L.iCycles (q + 1)
      comm₂₃ := by simp [cyclesBoundariesShortComplex] }
  have : Mono φ.τ₃ := mono_comp _ _
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ (L.cyclesIsKernel q (q + 1) (by simp))

/-- The short complex `Bᵠ⁺¹ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹` of boundaries, cycles and cohomology of `L`. -/
noncomputable def boundariesHomologyShortComplex (q : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (Limits.image.ι (L.toCycles q (q + 1))) (L.homologyπ (q + 1)) (by
    rw [← cancel_epi (factorThruImage (L.toCycles q (q + 1))), comp_zero, ← Category.assoc,
      Limits.image.fac, HomologicalComplex.toCycles_comp_homologyπ])

/-- The sequence `0 ⟶ Bᵠ⁺¹ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹ ⟶ 0` is short exact. -/
lemma shortExact_boundariesHomologyShortComplex (q : ℕ) :
    (boundariesHomologyShortComplex L q).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ (inferInstanceAs (Mono (Limits.image.ι _)))
    (inferInstanceAs (Epi (L.homologyπ (q + 1))))
  let φ : ShortComplex.mk _ _ (L.toCycles_comp_homologyπ q (q + 1)) ⟶
      boundariesHomologyShortComplex L q :=
    { τ₁ := factorThruImage (L.toCycles q (q + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [boundariesHomologyShortComplex] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (factorThruImage _))
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_g_is_cokernel _ (L.homologyIsCokernel q (q + 1) (by simp))

variable (hL : ∀ j m, Subsingleton ((L.X j).H (m + 1)))
  (hH : ∀ q m, Subsingleton ((L.homology q).H (m + 1)))

include hL in
/-- If the terms `Lʲ` and the cycles `Zʲ` of `L` are acyclic, then so is the image `Bʲ⁺¹` of the
differential `Lʲ ⟶ Zʲ⁺¹`, by the sequence `0 ⟶ Zʲ ⟶ Lʲ ⟶ Bʲ⁺¹ ⟶ 0`. -/
lemma subsingleton_H_image (j : ℕ) (hZ : ∀ m, Subsingleton ((L.cycles j).H (m + 1))) (m : ℕ) :
    Subsingleton ((Limits.image (L.toCycles j (j + 1))).H (m + 1)) := by
  have hS := shortExact_cyclesBoundariesShortComplex L j
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : (cyclesBoundariesShortComplex L j).X₃.H (m + 1), z = 0 by rw [h x, h y]
  intro z
  have hz : z ∈ (H.δ hS (m + 1)).ker := by
    have : Subsingleton ((cyclesBoundariesShortComplex L j).X₁.H (m + 1 + 1)) := hZ (m + 1)
    rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _
  rw [H.ker_δ_eq_range_map_g] at hz
  obtain ⟨w, rfl⟩ := hz
  have : Subsingleton ((cyclesBoundariesShortComplex L j).X₂.H (m + 1)) := hL j m
  rw [Subsingleton.elim w 0, map_zero]

include hL hH in
/-- If the terms and the cohomology sheaves of `L` are acyclic, so are its cycles `Zʲ`: by
induction on `j`, using `0 ⟶ Bʲ⁺¹ ⟶ Zʲ⁺¹ ⟶ Hʲ⁺¹ ⟶ 0`. -/
lemma subsingleton_H_cycles : ∀ j m, Subsingleton ((L.cycles j).H (m + 1))
  | 0, m => by
    have := L.isIso_homologyπ 0 0 (by simp) (by simp)
    have := hH 0 m
    exact subsingleton_H_of_iso (asIso (L.homologyπ 0)).symm (m + 1)
  | j + 1, m => by
    have : Subsingleton ((boundariesHomologyShortComplex L j).X₁.H (m + 1)) :=
      subsingleton_H_image L hL j (subsingleton_H_cycles j) m
    have : Subsingleton ((boundariesHomologyShortComplex L j).X₃.H (m + 1)) := hH (j + 1) m
    exact subsingleton_H_X₂_of_shortExact (shortExact_boundariesHomologyShortComplex L j) (m + 1)

include hL hH in
/-- **Sections of the cohomology sheaves of a complex.** If the terms and the cohomology sheaves
of a complex `L` of `𝒪_X`-modules are acyclic, then `Γ(X, Hᵠ⁺¹(L)) ≅ Γ(X, Zᵠ⁺¹) / Γ(X, Lᵠ)`:
global sections commute with the cohomology of `L`. -/
lemma surjective_app_homologyπ (q : ℕ) : Function.Surjective ((L.homologyπ (q + 1)).app ⊤).hom :=
  have : Subsingleton ((boundariesHomologyShortComplex L q).X₁.H 1) :=
    subsingleton_H_image L hL q (subsingleton_H_cycles L hL hH q) 0
  surjective_app_g_of_subsingleton (shortExact_boundariesHomologyShortComplex L q)

include hL hH in
lemma ker_app_homologyπ (q : ℕ) :
    ((L.homologyπ (q + 1)).app ⊤).hom.ker = ((L.toCycles q (q + 1)).app ⊤).hom.range := by
  refine (range_app_f_eq_ker_app_g (shortExact_boundariesHomologyShortComplex L q)).symm.trans ?_
  have : Subsingleton ((cyclesBoundariesShortComplex L q).X₁.H 1) :=
    subsingleton_H_cycles L hL hH q 0
  have hsurj := surjective_app_g_of_subsingleton (shortExact_cyclesBoundariesShortComplex L q)
  change ((Limits.image.ι (L.toCycles q (q + 1))).app ⊤).hom.range = _
  conv_rhs => rw [← Limits.image.fac (L.toCycles q (q + 1))]
  have hsurj' : Function.Surjective ((factorThruImage (L.toCycles q (q + 1))).app ⊤).hom := hsurj
  rw [Hom.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.range_comp,
    AddMonoidHom.range_eq_top.mpr hsurj', ← AddMonoidHom.range_eq_map]

/-- `Γ(X, Hᵠ⁺¹(L)) ≅ Γ(X, Zᵠ⁺¹) / Γ(X, Lᵠ)` when the terms and the cohomology sheaves of `L` are
acyclic. -/
noncomputable def homologySectionsAddEquiv (q : ℕ) :
    Γ(L.homology (q + 1), ⊤) ≃+ Γ(L.cycles (q + 1), ⊤) ⧸
      ((L.toCycles q (q + 1)).app ⊤).hom.range :=
  ((QuotientAddGroup.quotientAddEquivOfEq (ker_app_homologyπ L hL hH q)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_app_homologyπ L hL hH q))).symm
end CohomologySheaves

end AlgebraicGeometry.Scheme.Modules
