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

end Shift
end AlgebraicGeometry.Scheme.Modules
