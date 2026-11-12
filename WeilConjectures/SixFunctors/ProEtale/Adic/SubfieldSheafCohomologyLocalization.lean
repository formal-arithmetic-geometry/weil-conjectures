/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersPadicIntBasis
public import WeilConjectures.NumberTheory.Padics.Logarithm
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafCohomology

/-!
# `H^q(X_proét, E_X)` as a localization of `H^q(X_proét, 𝒪_{E,X})`

Let `X` be a quasi-compact quasi-separated scheme and `E ⊆ ℚ̄_ℓ` a subfield with ring of integers
`𝒪_E`. Since `E_X` is the filtered colimit of `𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯`
(`AlgebraicGeometry.ProEtale.H_padicSubfieldSheaf`), the map
`H^q(X_proét, 𝒪_{E,X}) ⟶ H^q(X_proét, E_X)` is the localization at the powers of `ℓ`, as soon as
`H^q(X_proét, 𝒪_{E,X})` has no `ℓ`-torsion. Hence an additive isomorphism
`H^q(X_proét, 𝒪_{E,X}) ≅ 𝒪_E` induces one `H^q(X_proét, E_X) ≅ E`.

## Main statements

- `AlgebraicGeometry.ProEtale.isLocalizedModule_H_padicSubfieldSheaf`: the localization statement.
- `AlgebraicGeometry.ProEtale.nonempty_addEquiv_H_padicSubfieldSheaf_of_addEquiv`: from
  `H^q(X_proét, 𝒪_{E,X}) ≅ 𝒪_E` to `H^q(X_proét, E_X) ≅ E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl

namespace AlgebraicGeometry.ProEtale

section Mul

variable (X : Scheme.{u}) (R : Type) [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]

lemma continuousMapAbSheafMul_add (a b : R) :
    continuousMapAbSheafMul X R (a + b) =
      continuousMapAbSheafMul X R a + continuousMapAbSheafMul X R b := by
  ext U f
  exact congrArg ULift.up (ContinuousMap.ext fun x ↦ add_mul _ _ _)

lemma continuousMapAbSheafMul_one : continuousMapAbSheafMul X R 1 = 𝟙 _ := by
  ext U f
  exact congrArg ULift.up (ContinuousMap.ext fun x ↦ one_mul _)

lemma continuousMapAbSheafMul_zero : continuousMapAbSheafMul X R 0 = 0 := by
  ext U f
  exact congrArg ULift.up (ContinuousMap.ext fun x ↦ zero_mul _)

/-- Multiplication by `n : ℕ` on `C(-, R)` induces multiplication by `n` on cohomology. -/
lemma H_map_continuousMapAbSheafMul_natCast (n q : ℕ)
    (y : Sheaf.H (continuousMapAbSheaf X R) q) :
    Sheaf.H.map (continuousMapAbSheafMul X R (n : R)) q y = n • y := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, continuousMapAbSheafMul_zero, zero_smul, Sheaf.H.map_apply,
      Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  | succ n ih =>
    rw [Nat.cast_succ, continuousMapAbSheafMul_add, Sheaf.H.map_add_apply, ih,
      continuousMapAbSheafMul_one, Sheaf.H.map_id_apply, succ_nsmul]

end Mul

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]

/-- The transition map `n ⟶ n + k` of the tower `𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯` induces
multiplication by `ℓᵏ` on cohomology. -/
lemma H_map_padicIntegersSheafMulSequence_map (n k q : ℕ) :
    letI := normedFieldOfAlgebra l E
    ∀ y : Sheaf.H (continuousMapAbSheaf X (integers l E)) q,
      Sheaf.H.map ((padicIntegersSheafMulSequence X l E).map (homOfLE (n.le_add_right k))) q y =
        l ^ k • y := by
  let := normedFieldOfAlgebra l E
  intro y
  induction k with
  | zero =>
    rw [pow_zero, one_smul]
    exact (congrArg (fun f ↦ Sheaf.H.map f q y)
      ((padicIntegersSheafMulSequence X l E).map_id n)).trans (Sheaf.H.map_id_apply _)
  | succ k ih =>
    rw [show homOfLE (n.le_add_right (k + 1)) =
        homOfLE (n.le_add_right k) ≫ homOfLE ((n + k).le_add_right 1) from rfl,
      Functor.map_comp, Sheaf.H.map_comp_apply, ih, map_nsmul,
      padicIntegersSheafMulSequence_map_succ]
    erw [H_map_continuousMapAbSheafMul_natCast X (integers l E) l q y]
    rw [← mul_nsmul, pow_succ, mul_comm]

/-- The legs `ℓ⁻ⁿ : H^q(𝒪_{E,X}) ⟶ H^q(E_X)` satisfy `ι_n y = ι_{n+k} (ℓᵏ y)`. -/
lemma H_map_padicSubfieldSheafCocone_ι_app (q n k : ℕ) :
    letI := normedFieldOfAlgebra l E
    ∀ y : Sheaf.H (continuousMapAbSheaf X (integers l E)) q,
      Sheaf.H.map ((padicSubfieldSheafCocone X l E).ι.app n) q y =
        Sheaf.H.map ((padicSubfieldSheafCocone X l E).ι.app (n + k)) q (l ^ k • y) := by
  let := normedFieldOfAlgebra l E
  intro y
  rw [← H_map_padicIntegersSheafMulSequence_map, ← Sheaf.H.map_comp_apply,
    (padicSubfieldSheafCocone X l E).w]
  rfl

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- **`H^q(X_proét, E_X) = H^q(X_proét, 𝒪_{E,X})[1/ℓ]`.** On a quasi-compact quasi-separated
scheme, if `H^q(X_proét, 𝒪_{E,X})` has no `ℓ`-torsion, the map
`H^q(X_proét, 𝒪_{E,X}) ⟶ H^q(X_proét, E_X)` is the localization at the powers of `ℓ` (as a map
of abelian groups). -/
theorem isLocalizedModule_H_padicSubfieldSheaf (q : ℕ)
    (htf : letI := normedFieldOfAlgebra l E
      ∀ (k : ℕ) (y : Sheaf.H (continuousMapAbSheaf X (integers l E)) q), l ^ k • y = 0 → y = 0) :
    letI := normedFieldOfAlgebra l E
    IsLocalizedModule (Submonoid.powers (l : ℤ))
      (Sheaf.H.map ((padicSubfieldSheafCocone X l E).ι.app 0) q).toIntLinearMap := by
  let := normedFieldOfAlgebra l E
  obtain ⟨h₁, h₂⟩ := H_padicSubfieldSheaf X l E q
  let ι (n : ℕ) := Sheaf.H.map ((padicSubfieldSheafCocone X l E).ι.app n) q
  have hι (n k : ℕ) (y) : ι n y = ι (n + k) (l ^ k • y) :=
    H_map_padicSubfieldSheafCocone_ι_app X l E q n k y
  -- a class killed in `H^q(E_X)` is killed by a power of `ℓ`
  have hker (n : ℕ) (y) (hy : ι n y = 0) : ∃ k, l ^ k • y = 0 := by
    obtain ⟨m, a, ha⟩ := h₂ n y hy
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom a)
    exact ⟨k, (H_map_padicIntegersSheafMulSequence_map X l E n k q y).symm.trans ha⟩
  have hunit : IsUnit (algebraMap ℤ (Module.End ℤ (Sheaf.H (continuousMapAbSheaf X E) q))
      (l : ℤ)) := by
    refine (Module.End.isUnit_iff _).2 ⟨fun x x' hxx' ↦ ?_, fun x ↦ ?_⟩
    · rw [← sub_eq_zero]
      obtain ⟨n, y, hy⟩ := h₁ (x - x')
      simp only [Module.algebraMap_end_apply] at hxx'
      have h0 : ι n (l • y) = 0 := by
        change Sheaf.H.map _ q (l • y) = 0
        rw [map_nsmul]
        erw [hy]
        rw [← natCast_zsmul, smul_sub, hxx', sub_self]
      obtain ⟨k, hk⟩ := hker n _ h0
      rw [← mul_nsmul, ← pow_succ'] at hk
      rw [← hy, htf _ y hk, map_zero]
    · obtain ⟨n, y, rfl⟩ := h₁ x
      refine ⟨ι (n + 1) y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [hι n 1, pow_one, map_nsmul, natCast_zsmul]
  constructor
  · rintro ⟨_, k, rfl⟩
    rw [map_pow]
    exact hunit.pow k
  · intro x
    obtain ⟨n, y, rfl⟩ := h₁ x
    refine ⟨⟨y, ⟨(l : ℤ) ^ n, n, rfl⟩⟩, ?_⟩
    change ((l : ℤ) ^ n) • ι n y = ι 0 y
    rw [hι 0 n, zero_add, map_nsmul, ← Nat.cast_pow, natCast_zsmul]
  · intro y y' hyy'
    obtain ⟨k, hk⟩ := hker 0 (y - y') (by
      rw [map_sub]
      exact sub_eq_zero.2 hyy')
    refine ⟨⟨(l : ℤ) ^ k, k, rfl⟩, ?_⟩
    change ((l : ℤ) ^ k) • y = ((l : ℤ) ^ k) • y'
    rw [← sub_eq_zero, ← smul_sub, ← Nat.cast_pow, natCast_zsmul, hk]

/-- On a quasi-compact quasi-separated scheme, an additive isomorphism
`H^q(X_proét, 𝒪_{E,X}) ≅ 𝒪_E` induces an additive isomorphism `H^q(X_proét, E_X) ≅ E`: both are
the localizations at `ℓ` (`AlgebraicGeometry.ProEtale.isLocalizedModule_H_padicSubfieldSheaf`,
`PadicAlgCl.isLocalizedModule_integers_subtype`). -/
theorem nonempty_addEquiv_H_padicSubfieldSheaf_of_addEquiv (q : ℕ)
    (ψ : letI := normedFieldOfAlgebra l E
      Sheaf.H (continuousMapAbSheaf X (integers l E)) q ≃+ integers l E) :
    letI := normedFieldOfAlgebra l E
    Nonempty (Sheaf.H (continuousMapAbSheaf X E) q ≃+ E) := by
  let := normedFieldOfAlgebra l E
  have htf (k : ℕ) (y : Sheaf.H (continuousMapAbSheaf X (integers l E)) q)
      (hy : l ^ k • y = 0) : y = 0 := by
    refine ψ.injective ((map_zero ψ).symm ▸ Subtype.ext ?_)
    have h := congrArg (fun z : integers l E ↦ (z : E)) ((map_nsmul ψ _ y).symm.trans
      ((congrArg ψ hy).trans (map_zero ψ)))
    simp only [ZeroMemClass.coe_zero, nsmul_eq_mul, Nat.cast_pow] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ natCast_ne_zero_of_algebra)
  have := isLocalizedModule_H_padicSubfieldSheaf X l E q htf
  have := isLocalizedModule_integers_subtype l E
  exact ⟨(IsLocalizedModule.linearEquiv (Submonoid.powers (l : ℤ))
    (Sheaf.H.map ((padicSubfieldSheafCocone X l E).ι.app 0) q).toIntLinearMap
    ((integers l E).subtype.toAddMonoidHom.toIntLinearMap ∘ₗ
      ψ.toIntLinearEquiv.toLinearMap)).toAddEquiv⟩

end AlgebraicGeometry.ProEtale
