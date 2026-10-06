/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
public import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category

/-!
# Serre's theorems on the cohomology of projective schemes

This file states, for the Picard-framework block of the blueprint, the three results of
Serre's *Faisceaux algébriques cohérents* that the rest of the block uses: the computation of
the cohomology of the twisting sheaves on projective space, and Serre's theorems A and B for a
coherent sheaf on a closed subscheme of projective space.

Theorem B is proved from the cohomology of the twisting sheaves: a coherent module on `ℙᵈ_k`
is a quotient of a finite sum of twists `𝒪(-m)` with coherent kernel, and descending induction
on the degree in the long exact cohomology sequence gives Serre vanishing on `ℙᵈ_k`; a closed
subscheme reduces to `ℙᵈ_k` by pushing forward. Serre vanishing for an ample invertible module
follows.

Projective space is the project's relative projective space `ℙ(n; S)`, whose index type `n` is
the index type of the *homogeneous* coordinates, so that `ℙᵈ_k` is `ℙ(n; Spec k)` for a type
`n` with `Nat.card n = d + 1`.

The twisting sheaf `AlgebraicGeometry.ProjectiveSpace.twist` is the pullback along
`AlgebraicGeometry.ProjectiveSpace.toProjInt` of `AlgebraicGeometry.Proj.twist` of the integral
model `Proj ℤ[Tᵢ]`, and `AlgebraicGeometry.ProjectiveSpace.twistRestrict` is its pullback to a
closed subscheme.

## Implementation notes

The symmetric power `Sᵐ(V)` of `V = k^{d+1}` is realised as the degree-`m` homogeneous part
`MvPolynomial.homogeneousSubmodule n k m` of the polynomial ring in the homogeneous
coordinates. Mathlib's `SymmetricPower R ι M` forces the index type `ι` to lie in the same
universe as the ring `R`, which does not fit `Sym^m` for a field in an arbitrary universe, and
the homogeneous part is anyway the object Serre's theorem produces.

Mathlib has no `IsCoherent` predicate for sheaves of modules; "coherent" is spelled here as
`SheafOfModules.IsFinitePresentation` together with `SheafOfModules.IsQuasicoherent`, which
agrees with coherence on a noetherian scheme such as a closed subscheme of `ℙᵈ_k`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.nonempty_H_zero_twist_equiv`,
  `subsingleton_H_twist_of_ne`, `subsingleton_H_twist_top` and
  `nonempty_H_twist_top_equiv_dual` — the cohomology of `𝒪(m)` on `ℙᵈ_k`.
- `AlgebraicGeometry.Scheme.Modules.exists_tensorPowHom_eq` — clearing denominators for a
  section of an invertible module.
- `AlgebraicGeometry.ProjectiveSpace.exists_epi_sigma_twist` — a coherent module on `ℙⁿ_A` is a
  quotient of a finite sum of twists `𝒪(-m)`.
- `AlgebraicGeometry.ProjectiveSpace.exists_subsingleton_H_tensor_twist` — Serre vanishing on
  `ℙᵈ_k`: `H^q(ℙᵈ_k, ℱ(d)) = 0` for `q > 0` and `d ≫ 0`.
- `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist` — Serre's theorem B.
- `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensorObj_tensorPow` — Serre vanishing
  for an ample invertible module.
- `AlgebraicGeometry.Scheme.Modules.exists_generatingSections_tensor_twist` — Serre's
  theorem A.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry.Scheme.Modules

noncomputable section

namespace AlgebraicGeometry

variable (n : Type u)

section Pn

/-- **`H⁰` of the twisting sheaves on `ℙᵈ_k`.** With `X = ℙᵈ_k` presented as `ℙ(n; Spec k)`
for an index type `n` of homogeneous coordinates with `Nat.card n = d + 1`, and `Sᵐ(V)` for
`V = k^{d+1}` the degree-`m` homogeneous part of the polynomial ring in those coordinates,
`H⁰(X, 𝒪(m)) = Sᵐ(V)` for `m ≥ 0`.

(blueprint: `sk-thm-picard-pn`) -/
theorem ProjectiveSpace.nonempty_H_zero_twist_equiv (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hn : Nat.card n = d + 1) (m : ℕ) :
    Nonempty ((ProjectiveSpace.twist n (Spec (.of k)) m).H 0 ≃ₗ[k]
      MvPolynomial.homogeneousSubmodule n k m) :=
  sorry

/-- **Vanishing of the cohomology of the twisting sheaves in middle degrees.**
`H^q(ℙᵈ_k, 𝒪(m)) = 0` for every `m` and every `q ∉ {0, d}`.

(blueprint: `sk-thm-picard-pn`) -/
theorem ProjectiveSpace.subsingleton_H_twist_of_ne (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hn : Nat.card n = d + 1) (q : ℕ) (m : ℤ) (hq0 : q ≠ 0) (hqd : q ≠ d) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H q) :=
  sorry

/-- **Vanishing of the top cohomology of the twisting sheaves.**
`H^d(ℙᵈ_k, 𝒪(m)) = 0` for `m ≥ -d`, when `d ≠ 0`. For `d = 0` the statement is false, since
`H⁰(Spec k, 𝒪) = k`; that case is `nonempty_H_zero_twist_equiv` with `d = 0`.

(blueprint: `sk-thm-picard-pn`) -/
theorem ProjectiveSpace.subsingleton_H_twist_top (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hd : d ≠ 0) (hn : Nat.card n = d + 1) (m : ℤ) (hm : -(d : ℤ) ≤ m) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H d) :=
  sorry

/-- **The top cohomology of the twisting sheaves.**
`H^d(ℙᵈ_k, 𝒪(m)) = S^{-m-d-1}(V)^∨` for `m ≤ -d-1`. Taking `m = -d-1` exhibits `𝒪(-d-1)` as
the dualising sheaf of `ℙᵈ_k`.

(blueprint: `sk-thm-picard-pn`) -/
theorem ProjectiveSpace.nonempty_H_twist_top_equiv_dual (k : Type u) [Field k] [Finite n]
    (d : ℕ) (hn : Nat.card n = d + 1) (m : ℤ) (hm : m ≤ -(d : ℤ) - 1) :
    Nonempty ((ProjectiveSpace.twist n (Spec (.of k)) m).H d ≃ₗ[k]
      Module.Dual k (MvPolynomial.homogeneousSubmodule n k (-m - d - 1).toNat)) :=
  sorry

end Pn

section ClearingDenominators

variable {X : Scheme.{u}}

/-- **Clearing denominators for a section of an invertible module.** Let `X` be quasi-compact
and separated over an affine scheme `S`, let `ℒ` be an invertible `𝒪_X`-module and
`s : 𝒪_X ⟶ ℒ` a global section, with zero scheme `Z(s)` and complement `X_s = X ∖ Z(s)`. For
every quasi-coherent `𝒪_X`-module `ℱ` and every section `t` of `ℱ` over `X_s`, there are `m ≥ 0`
and a global section `u` of `ℱ ⊗ ℒ^{⊗ m}` whose restriction to `X_s` is `t ⊗ s^{⊗ m}`.

Here `t ⊗ s^{⊗ m}` is the image of `t` under `ℱ ≅ ℱ ⊗ 𝒪_X ⟶ ℱ ⊗ ℒ^{⊗ m}`, the second map being
`ℱ ◁ s^{⊗ m}`.

On a finite affine cover `V_j` of `X` trivialising `ℒ`, with `s = f_j e_j`, one has
`X_s ∩ V_j = D(f_j)`, so `f_j^a t` lifts to `t_j ∈ Γ(V_j, ℱ)` for a common `a`; the overlaps
`V_j ∩ V_k` are affine since `X` is separated over an affine base, so the differences of the
`t_j ⊗ e_j^a` there are killed by a common power `f_j^b`, and the sections `t_j ⊗ e_j^a ⊗ s^b`
glue. Take `m = a + b`.

(blueprint: `lem-pc-section-clearing-denominators`) -/
@[stacks 01PW]
theorem Scheme.Modules.exists_tensorPowHom_eq {S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [IsSeparated f] [CompactSpace X] (ℒ : X.Modules) [ℒ.IsInvertible] (s : 𝟙_ X.Modules ⟶ ℒ)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    (t : Γ(ℱ, s.zeroLocus.support.compl)) :
    ∃ (m : ℕ) (u : Γ(ℱ ⊗ ℒ.tensorPow m, ⊤)),
      (ℱ ⊗ ℒ.tensorPow m).presheaf.map (homOfLE le_top).op u =
        ((ρ_ ℱ).inv ≫ ℱ ◁ tensorPowHom s m).app _ t :=
  sorry

end ClearingDenominators

section TwistQuotient

variable {n}

/-- **A coherent module is a quotient of a finite sum of twists.** Let `A` be noetherian and
`ℱ` a coherent module on `ℙⁿ_A = ℙ(n; Spec A)`. There are `m₁, …, m_r ≥ 0` and an epimorphism
`⨁ⱼ 𝒪(-mⱼ) ⟶ ℱ`, whose kernel is coherent.

On each standard chart `D₊(Tᵢ)` choose finitely many generators `tᵢₐ` of `ℱ`. Clearing
denominators (`AlgebraicGeometry.Scheme.Modules.exists_tensorPowHom_eq`, applied to the section
`Tᵢ` of `𝒪(1)`, `ℙⁿ_A` being separated over `Spec A`) extends `tᵢₐ ⊗ Tᵢ^{mᵢₐ}` to a global
section of `ℱ(mᵢₐ)`, i.e. to a map `𝒪(-mᵢₐ) ⟶ ℱ` whose image contains `tᵢₐ` on `D₊(Tᵢ)`. The
sum of these maps is surjective on every chart, hence surjective. Its kernel is coherent, the
charts being spectra of noetherian rings.

(blueprint: `lem-pc-projective-space-twist-quotient`) -/
theorem ProjectiveSpace.exists_epi_sigma_twist (A : Type u) [CommRing A] [IsNoetherianRing A]
    [Finite n] (ℱ : (ℙ(n; Spec (.of A))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ] :
    ∃ (r : ℕ) (m : Fin r → ℕ)
      (p : (∐ fun j ↦ ProjectiveSpace.twist n (Spec (.of A)) (-(m j : ℤ))) ⟶ ℱ), Epi p ∧
      SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) (kernel p) ∧
      SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf) (kernel p) :=
  sorry

end TwistQuotient

section SerreVanishing

variable {n} (k : Type u) [Field k]

/-- On a projective space without homogeneous coordinates, which is empty, all cohomology
vanishes. -/
lemma ProjectiveSpace.subsingleton_H_of_isEmpty [IsEmpty n] (S : Scheme.{u})
    (ℱ : (ℙ(n; S)).Modules) (q : ℕ) : Subsingleton (ℱ.H q) :=
  subsingleton_H_of_isZero (isZero_of_isEmpty ℱ) q

/-- `H^q(ℙᵈ_k, 𝒪(e)) = 0` for `q > 0` and `e ≥ 0`, from `subsingleton_H_twist_of_ne` and
`subsingleton_H_twist_top`. -/
lemma ProjectiveSpace.subsingleton_H_twist_of_pos [Finite n] {d : ℕ} (hn : Nat.card n = d + 1)
    {q : ℕ} (hq : 0 < q) {e : ℤ} (he : 0 ≤ e) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) e).H q) := by
  by_cases hqd : q = d
  · subst hqd
    exact ProjectiveSpace.subsingleton_H_twist_top n k q hq.ne' hn e (by omega)
  · exact ProjectiveSpace.subsingleton_H_twist_of_ne n k d hn q e hq.ne' hqd

/-- **Serre vanishing on projective space.** Let `ℱ` be a coherent module on `ℙᵈ_k`. There is
`d₀` such that `H^q(ℙᵈ_k, ℱ(d)) = 0` for all `d ≥ d₀` and all `q > 0`.

By descending induction on `q`, for all coherent modules at once. For `q > d` the cohomology
vanishes (`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_isClosedImmersion`). In general,
`AlgebraicGeometry.ProjectiveSpace.exists_epi_sigma_twist` gives `0 ⟶ 𝒦 ⟶ ⨁ⱼ 𝒪(-mⱼ) ⟶ ℱ ⟶ 0`
with `𝒦` coherent; twisting by the invertible `𝒪(d)` keeps it exact, and in its long exact
sequence `⨁ⱼ H^q(𝒪(d - mⱼ)) ⟶ H^q(ℱ(d)) ⟶ H^{q+1}(𝒦(d))` the left term vanishes for
`d ≥ maxⱼ mⱼ` and the right one for `d ≫ 0` by induction.

The blueprint states this over a noetherian ring `A`; it is stated here over a field, where
the cohomology of the twisting sheaves
(`AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_of_ne` and `subsingleton_H_twist_top`)
is available.

(blueprint: `lem-pc-projective-space-serre-vanishing`) -/
theorem ProjectiveSpace.exists_subsingleton_H_tensor_twist [Finite n]
    (ℱ : (ℙ(n; Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of k))).ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of k))).ringCatSheaf) ℱ] :
    ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ q : ℕ, 0 < q →
      Subsingleton ((ℱ ⊗ ProjectiveSpace.twist n (Spec (.of k)) d).H q) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨0, fun d _ q _ ↦ ProjectiveSpace.subsingleton_H_of_isEmpty _ _ q⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, Nat.card n = D + 1 :=
    ⟨Nat.card n - 1, by have := Nat.card_pos (α := n); omega⟩
  suffices key : ∀ j : ℕ, ∀ (𝒢 : (ℙ(n; Spec (.of k))).Modules)
      [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of k))).ringCatSheaf) 𝒢]
      [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of k))).ringCatSheaf) 𝒢],
      ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ q : ℕ, D < q + j → 0 < q →
        Subsingleton ((𝒢 ⊗ ProjectiveSpace.twist n (Spec (.of k)) d).H q) by
    obtain ⟨d₀, h⟩ := key (D + 1) ℱ
    exact ⟨d₀, fun d hd q hq ↦ h d hd q (by omega) hq⟩
  intro j
  induction j with
  | zero =>
    intro 𝒢 _ _
    refine ⟨0, fun d _ q hq _ ↦ ?_⟩
    have := isQuasicoherent_tensorObj 𝒢 (ProjectiveSpace.twist n (Spec (.of k)) d)
    exact subsingleton_H_of_isClosedImmersion k (𝟙 _) _ hD (by omega)
  | succ j ih =>
    intro 𝒢 _ _
    obtain ⟨r, m, p, hp, hK₁, hK₂⟩ := ProjectiveSpace.exists_epi_sigma_twist k 𝒢
    obtain ⟨d₁, h₁⟩ := ih 𝒢
    obtain ⟨d₂, h₂⟩ := ih (kernel p)
    refine ⟨max (max d₁ d₂) (∑ i, (m i : ℤ)), fun d hd q hq hq0 ↦ ?_⟩
    have hd₁ : d₁ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
    have hd₂ : d₂ ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
    have hdm : ∀ i, (m i : ℤ) ≤ d := fun i ↦ le_trans
      (Finset.single_le_sum (f := fun i ↦ (m i : ℤ)) (fun i _ ↦ by positivity)
        (Finset.mem_univ i)) (le_trans (le_max_right _ _) hd)
    by_cases hqj : D < q + j
    · exact h₁ d hd₁ q hqj hq0
    -- twisting by `𝒪(d)` is an equivalence, with inverse twisting by `𝒪(-d)`
    let T := ProjectiveSpace.twist n (Spec (.of k)) d
    obtain ⟨e₁⟩ := ProjectiveSpace.nonempty_twist_tensorObj_iso n (Spec (.of k)) d (-d)
    obtain ⟨e₂⟩ := ProjectiveSpace.nonempty_twist_tensorObj_iso n (Spec (.of k)) (-d) d
    let E := tensorRightEquivalence T (ProjectiveSpace.twist n (Spec (.of k)) (-d))
      (e₁ ≪≫ eqToIso (congrArg _ (add_neg_cancel d)) ≪≫
        (ProjectiveSpace.unitIsoTwistZero n (Spec (.of k))).symm)
      (e₂ ≪≫ eqToIso (congrArg _ (neg_add_cancel d)) ≪≫
        (ProjectiveSpace.unitIsoTwistZero n (Spec (.of k))).symm)
    have : (tensorRight T).IsEquivalence := E.isEquivalence_functor
    have hS : (ShortComplex.kernelSequence p).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact p) inferInstance hp
    have hS' := hS.map_of_exact (tensorRight T)
    let G := fun i ↦ ProjectiveSpace.twist n (Spec (.of k)) (-(m i : ℤ))
    have : ∀ i, Subsingleton ((G i ⊗ T).H q) := fun i ↦ by
      obtain ⟨e⟩ := ProjectiveSpace.nonempty_twist_tensorObj_iso n (Spec (.of k)) (-(m i : ℤ)) d
      have := ProjectiveSpace.subsingleton_H_twist_of_pos k hD hq0 (e := -(m i : ℤ) + d)
        (by have := hdm i; omega)
      exact subsingleton_H_of_iso e.symm q
    have hsum : Subsingleton ((∐ fun i ↦ G i ⊗ T).H q) := subsingleton_H_sigma (fun i ↦ G i ⊗ T) q
    have h₂' : Subsingleton (((tensorRight T).obj (kernel p)).H (q + 1)) :=
      h₂ d hd₂ (q + 1) (by omega) (by omega)
    have h₃ : Subsingleton (((tensorRight T).obj (∐ G)).H q) :=
      @subsingleton_H_of_iso _ _ _ (PreservesCoproduct.iso (tensorRight T) G).symm q hsum
    exact @subsingleton_H_of_shortExact _ _ hS' q h₃ h₂'

end SerreVanishing

variable {n} {X : Scheme.{u}} (k : Type u) [Field k]

open scoped AlgebraicGeometry.Scheme.Modules in
/-- **Serre's theorem B: vanishing after a twist.** Let `X ⊆ ℙᵈ_k` be a closed subscheme, i.e. a
closed immersion `i : X ⟶ ℙ(n; Spec k)`, and let `ℱ` be a coherent sheaf on `X`. Then
`H^q(X, ℱ ⊗ 𝒪_X(m)) = 0` for all `q > 0` and all `m ≫ 0`, where `𝒪_X(m)` is the pullback along
`i` of the twisting sheaf `𝒪(m)`.

Mathlib has no `IsCoherent` predicate, so "coherent" is spelled as
`SheafOfModules.IsFinitePresentation` together with `SheafOfModules.IsQuasicoherent`; on the
noetherian scheme `X` these two conditions together are coherence.

The pushforward `i_* ℱ` is coherent
(`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pushforward_of_isClosedImmersion`), with
`i_* (ℱ ⊗ 𝒪_X(m)) ≅ (i_* ℱ)(m)` by the projection formula and
`H^q(X, ℱ ⊗ 𝒪_X(m)) ≅ H^q(ℙᵈ_k, i_* (ℱ ⊗ 𝒪_X(m)))`, so this is Serre vanishing on `ℙᵈ_k`,
`AlgebraicGeometry.ProjectiveSpace.exists_subsingleton_H_tensor_twist`, for `i_* ℱ`.

(blueprint: `sk-thm-picard-serre-b`) -/
theorem Scheme.Modules.exists_subsingleton_H_tensor_twist [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ, 0 < q →
      Subsingleton ((F ⊗ₘ ProjectiveSpace.twistRestrict i m).H q) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of k)) ↘ Spec (.of k))
  have := isQuasicoherent_pushforward_of_isAffineHom i F
  have := isFinitePresentation_pushforward_of_isClosedImmersion i F
  obtain ⟨m₀, h⟩ := ProjectiveSpace.exists_subsingleton_H_tensor_twist k ((pushforward i).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  have := h m hm q hq
  obtain ⟨e⟩ := nonempty_pushforward_tensorObj_pullback_iso i F
    (ProjectiveSpace.twist n (Spec (.of k)) m)
  obtain ⟨e'⟩ := nonempty_H_pushforward_addEquiv_of_isClosedImmersion i
    (F ⊗ₘ ProjectiveSpace.twistRestrict i m) q
  have := subsingleton_H_of_iso e q
  exact e'.toEquiv.symm.subsingleton

open scoped AlgebraicGeometry.Scheme.Modules in
/-- **Serre's theorem A: global generation after a twist.** Let `X ⊆ ℙᵈ_k` be a closed
subscheme, i.e. a closed immersion `i : X ⟶ ℙ(n; Spec k)`, and let `ℱ` be a coherent sheaf on
`X`. Then `ℱ ⊗ 𝒪_X(m)` is generated by its global sections for all `m ≫ 0`.

"Generated by its global sections" is `Nonempty (SheafOfModules.GeneratingSections _)`: the
sections `σ.s : σ.I → M.sections` of a `GeneratingSections` are by construction global
sections of `M`, and `σ.π : free σ.I ⟶ M` being an epimorphism is exactly the statement that
the map from the free module on those global sections is surjective as a map of sheaves.

As for theorem B, "coherent" is `SheafOfModules.IsFinitePresentation` together with
`SheafOfModules.IsQuasicoherent`.

(blueprint: `sk-thm-picard-serre-a`) -/
theorem Scheme.Modules.exists_generatingSections_tensor_twist [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀,
      Nonempty (SheafOfModules.GeneratingSections (F ⊗ₘ ProjectiveSpace.twistRestrict i m)) :=
  sorry


/-- **Serre vanishing for an ample module.** Let `X` be a scheme over a field `k`, `ℒ` an ample
invertible `𝒪_X`-module and `ℱ` a coherent `𝒪_X`-module. Then there is `n₀` with
`H^p(X, ℱ ⊗ ℒ^{⊗ n}) = 0` for all `n ≥ n₀` and all `p > 0`.

Some power `ℒ^{⊗ m}`, `m ≥ 1`, is `i^* 𝒪(1)` for a closed immersion `i : X ⟶ ℙᴺ_k`. For each of
the finitely many `0 ≤ r < m`, Serre's theorem B
(`AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist`) applied to
`ℱ ⊗ ℒ^{⊗ r}` gives `t_r` with `H^q(X, ℱ ⊗ ℒ^{⊗ (m t + r)}) = H^q(X, ℱ ⊗ ℒ^{⊗ r} ⊗ 𝒪_X(t)) = 0`
for `t ≥ t_r` and `q > 0`; take `n₀ = m · maxᵣ t_r` and write `n = m t + r`.

The blueprint asks `X` to be proper over `k`; this is not needed here, since
`AlgebraicGeometry.IsVeryAmple` already provides a closed immersion into projective space.

(blueprint: `lem-pc-serre-vanishing`) -/
@[stacks 0B5U]
theorem Scheme.Modules.exists_subsingleton_H_tensorObj_tensorPow (f : X ⟶ Spec (.of k))
    (ℒ : X.Modules) [ℒ.IsInvertible] (hℒ : IsAmple f ℒ) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℕ, 0 < p → Subsingleton ((ℱ ⊗ ℒ.tensorPow n).H p) := by
  obtain ⟨m, hm, N, i, hN, hi, -, ⟨e⟩⟩ := hℒ
  have key (r : Fin m) : ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ p : ℕ, 0 < p →
      Subsingleton (((ℱ ⊗ ℒ.tensorPow r) ⊗ ProjectiveSpace.twistRestrict i t).H p) := by
    have := isQuasicoherent_tensorObj ℱ (ℒ.tensorPow r)
    have := isFinitePresentation_tensorObj ℱ (ℒ.tensorPow r)
    obtain ⟨m₀, h⟩ := exists_subsingleton_H_tensor_twist k i (ℱ ⊗ ℒ.tensorPow r)
    exact ⟨m₀.toNat, fun t ht p hp ↦ h t (by omega) p hp⟩
  choose t₀ ht₀ using key
  refine ⟨m * ∑ r, t₀ r, fun n hn p hp ↦ ?_⟩
  -- write `n = r + m t` with `r < m`
  set r : Fin m := ⟨n % m, Nat.mod_lt n hm⟩
  set t := n / m
  have hn' : n = r + m * t := (Nat.mod_add_div n m).symm
  have ht : t₀ r ≤ t := by
    refine le_trans (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r)) ?_
    exact (Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact hn)
  -- `ℒ^{⊗ m t} ≅ 𝒪_X(t)`
  have hpow : ∀ s : ℕ, Nonempty ((ℒ.tensorPow m).tensorPow s ≅
      (ProjectiveSpace.twistRestrict i 1).tensorPow s) := by
    intro s
    induction s with
    | zero => exact ⟨Iso.refl _⟩
    | succ s ih => exact ⟨e.symm ⊗ᵢ ih.some⟩
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso i
    (ProjectiveSpace.twist N (Spec (.of k)) 1) t
  obtain ⟨e₂⟩ := ProjectiveSpace.nonempty_tensorPow_twist_one_iso N (Spec (.of k)) t
  let e₃ : ℒ.tensorPow n ≅ ℒ.tensorPow r ⊗ ProjectiveSpace.twistRestrict i t :=
    eqToIso (congrArg ℒ.tensorPow hn') ≪≫ ℒ.tensorPowAddIso r (m * t) ≪≫
      (Iso.refl _ ⊗ᵢ (ℒ.tensorPowMulIso m t ≪≫ (hpow t).some ≪≫ e₁.symm ≪≫
        (Scheme.Modules.pullback i).mapIso e₂))
  have := ht₀ r t ht p hp
  exact subsingleton_H_of_iso ((α_ _ _ _) ≪≫ (Iso.refl ℱ ⊗ᵢ e₃.symm)) p

end AlgebraicGeometry
