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
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.MonomialCech
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Serre's theorems on the cohomology of projective schemes

This file states, for the Picard-framework block of the blueprint, the three results of
Serre's *Faisceaux algébriques cohérents* that the rest of the block uses: the computation of
the cohomology of the twisting sheaves on projective space, and Serre's theorems A and B for a
coherent sheaf on a closed subscheme of projective space.

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
- `AlgebraicGeometry.ProjectiveSpace.exists_epi_sigma_twist` — a coherent module on `ℙⁿ_A` is a
  quotient of a finite sum of twists `𝒪(-mⱼ)`.
- `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist` — Serre's theorem B.
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

/-- **The Čech complex of `𝒪(m)` on the standard covering is the monomial Čech complex.** Let
`k` be a field and `Uᵢ = D₊(xᵢ)` the standard opens of `ℙ(n; Spec k)`. The sections of `𝒪(m)`
over `U_J = ⋂_{j ∈ J} U_j` are the degree-`m` part of `k[xᵢ, x_j⁻¹ : j ∈ J]`, the restriction
maps being the inclusions; so the Čech complex of `𝒪(m)` on the covering `(Uᵢ)ᵢ`, as a complex
of `k`-vector spaces, is `ProjectiveSpace.monomialCechComplex n k m`.

This is the first step of the proof of `lem-pc-projective-space-twist-cohomology`: the
transition rule `e_i^{(m)} = (x_i/x_j)^m e_j^{(m)}` of `def-pc-projective-space-twist`, a
well-defined gluing by `lem-pc-twist-cocycle`, identifies the section `(x^e / x_i^m) e_i^{(m)}`
on `U_J ⊆ U_i` with the Laurent monomial `xᵉ`.

(blueprint: `lem-pc-projective-space-twist-cohomology`, `def-pc-projective-space-twist`) -/
theorem ProjectiveSpace.nonempty_cechComplex_twist_iso_monomialCechComplex (k : Type u)
    [Field k] [Fintype n] (m : ℤ) :
    Nonempty (((ModuleCat.restrictScalars
        (Scheme.globalSectionsRingHom k (X := ℙ(n; Spec (.of k))))).mapHomologicalComplex _).obj
      ((cechComplexFunctor (ProjectiveSpace.standardOpen n (Spec (.of k)))).obj
        (ProjectiveSpace.twist n (Spec (.of k)) m).presheafModuleCat) ≅
      ProjectiveSpace.monomialCechComplex n k m) :=
  sorry

/-- **Cohomology vanishes above the number of projective coordinates.** For a commutative
ring `A`, `n` with `Nat.card n = d + 1` and a quasi-coherent module `ℱ` on `ℙᵈ_A = ℙ(n; Spec A)`,
`H^q(ℙᵈ_A, ℱ) = 0` for `q > d`: the alternating Čech complex of the `d + 1` standard opens,
which computes the cohomology of `ℱ` since their intersections are affine, has no terms above
degree `d`.

(blueprint: `lem-pc-projective-space-cohomology-bound`) -/
theorem ProjectiveSpace.subsingleton_H_of_lt (A : Type u) [CommRing A] [Finite n] {d : ℕ}
    (hn : Nat.card n = d + 1) (ℱ : (ℙ(n; Spec (.of A))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ] {q : ℕ}
    (hq : d < q) : Subsingleton (ℱ.H q) :=
  sorry

/-- **The cohomology of `𝒪(m)` on `ℙ(n; Spec k)` is that of the monomial Čech complex**,
as `k`-vector spaces: Leray's theorem for the standard affine covering of the separated scheme
`ℙ(n; Spec k)`, combined with `nonempty_cechComplex_twist_iso_monomialCechComplex`.

(blueprint: `lem-pc-projective-space-twist-cohomology`) -/
theorem ProjectiveSpace.nonempty_H_twist_linearEquiv_homology (k : Type u) [Field k]
    [Fintype n] (m : ℤ) (q : ℕ) :
    Nonempty ((ProjectiveSpace.twist n (Spec (.of k)) m).H q ≃ₗ[k]
      (ProjectiveSpace.monomialCechComplex n k m).homology q) := by
  let φ := Scheme.globalSectionsRingHom k (X := ℙ(n; Spec (.of k)))
  let K := (cechComplexFunctor (ProjectiveSpace.standardOpen n (Spec (.of k)))).obj
    (ProjectiveSpace.twist n (Spec (.of k)) m).presheafModuleCat
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated
    (ℙ(n; Spec (.of k)) ↘ Spec (.of k)) (ProjectiveSpace.standardOpen n (Spec (.of k)))
    (fun i ↦ ProjectiveSpace.isAffineOpen_standardOpen n _ i)
    (ProjectiveSpace.iSup_standardOpen n _)
    (ProjectiveSpace.twist n (Spec (.of k)) m) q
  obtain ⟨e₂⟩ := ProjectiveSpace.nonempty_cechComplex_twist_iso_monomialCechComplex n k m
  let e₃ : (ProjectiveSpace.twist n (Spec (.of k)) m).H q ≃ₗ[k]
      (ModuleCat.restrictScalars φ).obj (K.homology q) :=
    { e₁.symm.toAddEquiv with map_smul' := fun c x ↦ e₁.symm.map_smul (φ c) x }
  exact ⟨e₃ ≪≫ₗ ((ModuleCat.restrictScalarsHomologyIso φ K q).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso e₂).toLinearEquiv⟩

/-- **`H⁰` of the twisting sheaves on `ℙᵈ_k`.** With `X = ℙᵈ_k` presented as `ℙ(n; Spec k)`
for an index type `n` of homogeneous coordinates with `Nat.card n = d + 1`, and `Sᵐ(V)` for
`V = k^{d+1}` the degree-`m` homogeneous part of the polynomial ring in those coordinates,
`H⁰(X, 𝒪(m)) = Sᵐ(V)` for `m ≥ 0`.

(blueprint: `sk-thm-picard-pn`, `lem-pc-projective-space-twist-cohomology` (i)) -/
theorem ProjectiveSpace.nonempty_H_zero_twist_equiv (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hn : Nat.card n = d + 1) (m : ℕ) :
    Nonempty ((ProjectiveSpace.twist n (Spec (.of k)) m).H 0 ≃ₗ[k]
      MvPolynomial.homogeneousSubmodule n k m) := by
  have := Fintype.ofFinite n
  have : Nonempty n := (Nat.card_pos_iff.1 (by omega)).1
  obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology n k m 0
  exact ⟨e ≪≫ₗ ProjectiveSpace.monomialCechComplexHomologyZeroLinearEquiv n k m⟩

/-- **Vanishing of the cohomology of the twisting sheaves in middle degrees.**
`H^q(ℙᵈ_k, 𝒪(m)) = 0` for every `m` and every `q ∉ {0, d}`.

(blueprint: `sk-thm-picard-pn`, `lem-pc-projective-space-twist-cohomology`) -/
theorem ProjectiveSpace.subsingleton_H_twist_of_ne (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hn : Nat.card n = d + 1) (q : ℕ) (m : ℤ) (hq0 : q ≠ 0) (hqd : q ≠ d) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H q) := by
  have := Fintype.ofFinite n
  rcases lt_or_gt_of_ne hqd with hlt | hlt
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
    obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology n k m (q + 1)
    have h := (ProjectiveSpace.exactAt_monomialCechComplex n k m
      (by rwa [← Nat.card_eq_fintype_card]) q hlt).isZero_homology
    have : Subsingleton ((ProjectiveSpace.monomialCechComplex n k m).homology (q + 1)) :=
      (ModuleCat.isZero_iff_subsingleton).1 h
    exact e.toEquiv.subsingleton
  · exact ProjectiveSpace.subsingleton_H_of_lt n k hn _ hlt

/-- **Vanishing of the top cohomology of the twisting sheaves.**
`H^d(ℙᵈ_k, 𝒪(m)) = 0` for `m ≥ -d`, when `d ≠ 0`. For `d = 0` the statement is false, since
`H⁰(Spec k, 𝒪) = k`; that case is `nonempty_H_zero_twist_equiv` with `d = 0`.

(blueprint: `sk-thm-picard-pn`, `lem-pc-projective-space-twist-cohomology` (ii)) -/
theorem ProjectiveSpace.subsingleton_H_twist_top (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hd : d ≠ 0) (hn : Nat.card n = d + 1) (m : ℤ) (hm : -(d : ℤ) ≤ m) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H d) := by
  have := Fintype.ofFinite n
  obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology n k m d
  have := ProjectiveSpace.subsingleton_monomialCechComplex_homology_top (n := n) (A := k)
    (by rwa [← Nat.card_eq_fintype_card]) hd hm
  exact e.toEquiv.subsingleton

/-- **The top cohomology of the twisting sheaves.**
`H^d(ℙᵈ_k, 𝒪(m)) = S^{-m-d-1}(V)^∨` for `m ≤ -d-1`. Taking `m = -d-1` exhibits `𝒪(-d-1)` as
the dualising sheaf of `ℙᵈ_k`.

The blueprint's isomorphism is the canonical one induced by the multiplication pairing. Here it
is transported through the non-canonical identification
`nonempty_H_twist_linearEquiv_homology` with the monomial Čech complex, so the description by
the pairing (`monomialCechComplexHomologyTopLinearEquivDual_apply`) holds only on that
complex.

(blueprint: `sk-thm-picard-pn`, `lem-pc-projective-space-twist-cohomology` (ii),
`lem-pc-projective-space-serre-pairing`) -/
theorem ProjectiveSpace.nonempty_H_twist_top_equiv_dual (k : Type u) [Field k] [Finite n]
    (d : ℕ) (hn : Nat.card n = d + 1) (m : ℤ) (hm : m ≤ -(d : ℤ) - 1) :
    Nonempty ((ProjectiveSpace.twist n (Spec (.of k)) m).H d ≃ₗ[k]
      Module.Dual k (MvPolynomial.homogeneousSubmodule n k (-m - d - 1).toNat)) := by
  have := Fintype.ofFinite n
  obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology n k m d
  exact ⟨e ≪≫ₗ ProjectiveSpace.monomialCechComplexHomologyTopLinearEquivDual n k m
    (by rwa [← Nat.card_eq_fintype_card]) hm⟩

end Pn

variable {n}

/-- **A finite quotient by twists.** Let `A` be noetherian and `ℱ` a coherent module on
`ℙⁿ_A = ℙ(n; Spec A)`. There are integers `m₁, …, m_r ≥ 0` and a surjection
`⊕ⱼ 𝒪(-mⱼ) ⟶ ℱ`, whose kernel is again coherent. On the standard chart `D₊(xᵢ)` choose finitely
many generators of `ℱ`; clearing denominators, each becomes, after multiplication by a power
`xᵢ^m` of the section `xᵢ` of `𝒪(1)`, a global section of `ℱ(m)`, i.e. a morphism
`𝒪(-m) ⟶ ℱ`.

(blueprint: `lem-pc-projective-space-twist-quotient`) -/
theorem ProjectiveSpace.exists_epi_sigma_twist (A : Type u) [CommRing A] [IsNoetherianRing A]
    [Finite n] (F : (ℙ(n; Spec (.of A))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf) F] :
    ∃ (ι : Type u) (_ : Finite ι) (e : ι → ℕ)
      (φ : (∐ fun a ↦ ProjectiveSpace.twist n (Spec (.of A)) (-(e a : ℤ))) ⟶ F), Epi φ ∧
        SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) (kernel φ) ∧
        SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf)
          (kernel φ) :=
  sorry

variable {X : Scheme.{u}} (k : Type u) [Field k]

open scoped AlgebraicGeometry.Scheme.Modules in
/-- **Serre's theorem B: vanishing after a twist.** Let `X ⊆ ℙᵈ_k` be a closed subscheme, i.e. a
closed immersion `i : X ⟶ ℙ(n; Spec k)`, and let `ℱ` be a coherent sheaf on `X`. Then
`H^q(X, ℱ ⊗ 𝒪_X(m)) = 0` for all `q > 0` and all `m ≫ 0`, where `𝒪_X(m)` is the pullback along
`i` of the twisting sheaf `𝒪(m)`.

Mathlib has no `IsCoherent` predicate, so "coherent" is spelled as
`SheafOfModules.IsFinitePresentation` together with `SheafOfModules.IsQuasicoherent`; on the
noetherian scheme `X` these two conditions together are coherence.

(blueprint: `sk-thm-picard-serre-b`) -/
theorem Scheme.Modules.exists_subsingleton_H_tensor_twist [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ, 0 < q →
      Subsingleton ((F ⊗ₘ ProjectiveSpace.twistRestrict i m).H q) :=
  sorry

open scoped AlgebraicGeometry.Scheme.Modules in
open ProjectiveSpace in
/-- **Serre's theorem A: global generation after a twist.** Let `X ⊆ ℙᵈ_k` be a closed
subscheme, i.e. a closed immersion `i : X ⟶ ℙ(n; Spec k)`, and let `ℱ` be a coherent sheaf on
`X`. Then `ℱ ⊗ 𝒪_X(m)` is generated by its global sections for all `m ≫ 0`.

"Generated by its global sections" is `Nonempty (SheafOfModules.GeneratingSections _)`: the
sections `σ.s : σ.I → M.sections` of a `GeneratingSections` are by construction global
sections of `M`, and `σ.π : free σ.I ⟶ M` being an epimorphism is exactly the statement that
the map from the free module on those global sections is surjective as a map of sheaves.

As for theorem B, "coherent" is `SheafOfModules.IsFinitePresentation` together with
`SheafOfModules.IsQuasicoherent`.

The proof follows Hartshorne: `𝒢 = i_* ℱ` is coherent on `P = ℙ(n; Spec k)`, and is a
quotient `⊕ₐ 𝒪(-mₐ) ⟶ 𝒢` of a finite sum of twists (`ProjectiveSpace.exists_epi_sigma_twist`).
For `m ≥ max mₐ`, tensoring with the invertible module `𝒪(m)` gives a surjection
`⊕ₐ 𝒪(m - mₐ) ⟶ 𝒢(m)` from a sum of twists of non-negative degree, each generated by global
sections (`ProjectiveSpace.generatingSectionsTwist`). Finally `𝒢(m) ≅ i_* (ℱ(m))` by the
projection formula, and global generation descends along `i` because `i_*` is faithful
(`Scheme.Modules.GeneratingSections.ofPushforward`).

(blueprint: `sk-thm-picard-serre-a`, `thm-picard-serre-a`) -/
theorem Scheme.Modules.exists_generatingSections_tensor_twist [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀,
      Nonempty (SheafOfModules.GeneratingSections (F ⊗ₘ ProjectiveSpace.twistRestrict i m)) := by
  -- Step 1: `𝒢 = i_* ℱ` is coherent on `P`, and a quotient of a finite sum of twists.
  have : IsLocallyNoetherian ℙ(n; Spec (.of k)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of k)) ↘ Spec (.of k))
  have := isQuasicoherent_pushforward_of_isClosedImmersion i F
  have := isFinitePresentation_pushforward_of_isClosedImmersion i F
  obtain ⟨ι, _, e, φ, hφ, -, -⟩ := exists_epi_sigma_twist k ((pushforward i).obj F)
  obtain ⟨M, hM⟩ := (Set.finite_range e).bddAbove
  refine ⟨M, fun m hm ↦ ?_⟩
  -- Step 2: each `𝒪(-mₐ) ⊗ 𝒪(m) ≅ 𝒪(m - mₐ)` is generated by global sections.
  have hgen (a : ι) : Nonempty (SheafOfModules.GeneratingSections
      (twist n (Spec (.of k)) (-(e a : ℤ)) ⊗ₘ twist n (Spec (.of k)) m)) := by
    obtain ⟨t⟩ := nonempty_twist_tensorObj_iso n (Spec (.of k)) (-(e a : ℤ)) m
    have hd : -(e a : ℤ) + m = ((m - e a).toNat : ℕ) := by
      have := hM ⟨a, rfl⟩
      omega
    exact ⟨(SheafOfModules.GeneratingSections.equivOfIso (t ≪≫ eqToIso (by rw [hd]))).symm
      (generatingSectionsTwist n _ _)⟩
  -- Step 3: `- ⊗ 𝒪(m)` is an autoequivalence, so `φ ⊗ 𝒪(m)` is an epimorphism out of
  -- `(⊕ₐ 𝒪(-mₐ)) ⊗ 𝒪(m) ≅ ⊕ₐ (𝒪(-mₐ) ⊗ 𝒪(m))`.
  obtain ⟨t⟩ := nonempty_twist_tensorObj_iso n (Spec (.of k)) m (-m)
  have : (tensorRight (twist n (Spec (.of k)) m)).IsEquivalence :=
    (BraidedCategory.tensorRightEquivalence (twist n (Spec (.of k)) m)
      (twist n (Spec (.of k)) (-m))
        (t ≪≫ eqToIso (by simp) ≪≫ (unitIsoTwistZero n _).symm)).isEquivalence_functor
  have : Epi (φ ▷ twist n (Spec (.of k)) m) := (tensorRight _).map_epi φ
  let σ := ((SheafOfModules.GeneratingSections.equivOfIso
    (PreservesCoproduct.iso (tensorRight (twist n (Spec (.of k)) m)) _).symm)
      (SheafOfModules.GeneratingSections.sigma _ fun a ↦ (hgen a).some)).ofEpi
        (φ ▷ twist n (Spec (.of k)) m)
  -- Step 4: `𝒢 ⊗ 𝒪(m) ≅ i_* (ℱ ⊗ i^* 𝒪(m))`, and generation descends along `i`.
  obtain ⟨pf⟩ := nonempty_pushforward_tensorObj_pullback_iso i F (twist n (Spec (.of k)) m)
  exact ⟨GeneratingSections.ofPushforward i
    (SheafOfModules.GeneratingSections.equivOfIso pf.symm σ)⟩

end AlgebraicGeometry
