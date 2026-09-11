/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExactSequence
public import WeilConjectures.AlgebraicGeometry.Modules.Monoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# The Euler characteristic of a coherent sheaf

Let `X` be a scheme proper over a field `k` and let `F` be a coherent sheaf of `𝒪_X`-modules.
Each cohomology group `H^i(X, F)` is then a finite-dimensional `k`-vector space, and it
vanishes for `i` larger than the dimension of `X`, so that

`χ(X, F) = ∑ i, (-1)^i * dim_k H^i(X, F)`

is a well-defined integer, the *Euler characteristic* of `F`. This file defines it and proves
its two basic properties: it is additive on short exact sequences, and on an affine scheme it
is simply the dimension of the space of global sections.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.eulerChar` — the Euler characteristic `χ(X, F)`.
- `AlgebraicGeometry.Scheme.Modules.H.mapOver` and
  `AlgebraicGeometry.Scheme.Modules.H.δOver` — the maps of the long exact cohomology sequence,
  as `k`-linear maps rather than `Γ(X, 𝒪_X)`-linear ones.

## Main results

- `AlgebraicGeometry.Scheme.Modules.eulerChar_add_eulerChar` — additivity of the Euler
  characteristic on a short exact sequence of coherent sheaves.
- `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_finrank_H_zero` and
  `AlgebraicGeometry.Scheme.Modules.eulerChar_unit_pos` — on an affine scheme the Euler
  characteristic is `dim_k H^0(X, F) = dim_k Γ(X, F)`, and `χ(X, 𝒪_X) > 0` if `X` is nonempty.
- `AlgebraicGeometry.Scheme.Modules.eulerChar_congr` and
  `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_zero_of_isZero` — the Euler characteristic is
  an isomorphism invariant and vanishes on the zero sheaf.
- `AlgebraicGeometry.Scheme.Modules.eulerChar_pushforward` — the Euler characteristic is
  unchanged by the direct image along a finite morphism, granted the sorried isomorphism
  `H.pushforwardLinearEquiv` on cohomology.

## Implementation notes

* **Where properness is not needed it is not assumed.** The statements of
  `prop:deg-euler-finite-morphism` are recorded here for a finite morphism of `k`-schemes,
  without the properness of source and target that the blueprint's "projective schemes over
  `k`" carries: neither the invariance of cohomology along a finite morphism nor the
  projection formula uses it, and the projection formula involves no base field at all.
  Properness enters only where the Euler characteristic has to be a meaningful number, that
  is through `H.finite` and the vanishing above the dimension.

* **Proper rather than projective.** The blueprint states
  `prop:deg-cohomology-finiteness`, `def:deg-euler`, `lem:deg-euler-additive` and
  `lem:deg-euler-affine` for a *projective* scheme over `k`, and remarks that parts (1) and (2)
  of `prop:deg-cohomology-finiteness` hold for a *proper* scheme. This file is stated for
  proper `X`, a deliberate generalisation: it is what the proofs need, and it avoids depending
  on a notion of ampleness, which this project does not yet have.

* **`dim X` is the topological Krull dimension.** The blueprint's `dim X` is read as
  `topologicalKrullDim X`, the supremum of the lengths of chains of irreducible closed subsets
  of the underlying topological space of `X`. This is the only notion of dimension of a scheme
  available at this point, and for a scheme of finite type over a field it agrees with the
  usual one.

* **The definition of `χ` is junk-value robust.** `eulerChar` is a `finsum` over all `i : ℕ`.
  Since `Module.finrank` is `0` in infinite dimension, no finiteness hypothesis is needed to
  *write* the definition, and `eulerChar_eq_sum_range` identifies it with a finite sum as soon
  as a vanishing bound is available. Every statement that uses the value of `χ` does carry the
  properness and coherence hypotheses that make it meaningful.

* **Deliberate `sorry`s.** The following are *stated* here and left `sorry`, exactly as
  `WeilConjectures.AlgebraicGeometry.ChowLemma` states Chow's lemma without proving it. They
  are the open obligations of the blueprint chapter, not gaps in the arguments given here:
  `H.finite`, `H.subsingleton_of_topologicalKrullDim_lt`,
  `Scheme.exists_topologicalKrullDim_le`, `H.subsingleton_of_isAffine`,
  `isCoherent_pushforward_of_isFinite`, `H.pushforwardLinearEquiv`,
  `pushforwardTensorPullbackIso`,
  `pushforwardTensorPullbackIso_naturality_left` and
  `pushforwardTensorPullbackIso_naturality_right`. Everything else in this file is proved.

* Part (3) of `prop:deg-cohomology-finiteness`, the long exact cohomology sequence, is **not**
  restated here: it is proved in
  `WeilConjectures.AlgebraicGeometry.Cohomology.LongExactSequence` as
  `Scheme.Modules.H.exact₁`, `H.exact₂`, `H.exact₃` and `H.injective_map_f`, with the
  connecting map `H.δ` and its `k`-linearity `H.δ_smul_over`. That is the whole of the
  blueprint's part (3); it needs nothing about closed immersions, and it is used as-is in the
  proof of `eulerChar_add_eulerChar`.

* `Scheme.exists_topologicalKrullDim_le` — the finite-dimensionality of a scheme proper over a
  field — is not itself a numbered part of `prop:deg-cohomology-finiteness`, but without it
  part (2) is vacuous: `topologicalKrullDim X < i` never holds for a `i : ℕ` if the dimension
  is infinite. It is what turns part (2) into the bound the Euler characteristic consumes,
  and it is sorried alongside it.

## Blueprint

This file implements the notion (N8) of `sec:deg-cost` of the chapter on the degree of the
isogeny: `prop:deg-cohomology-finiteness` (parts (1), (2) and (4); part (3) is the long exact
sequence, already available), `def:deg-euler`, `lem:deg-euler-additive`,
`lem:deg-euler-affine` and `prop:deg-euler-finite-morphism`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Module MonoidalCategory

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-! ### Cohomological finiteness on a proper scheme over a field -/

/-- **A scheme proper over a field is finite-dimensional.**

This is not one of the numbered parts of `prop:deg-cohomology-finiteness`, but it is what makes
part (2) of that proposition — the vanishing of `H^i(X, F)` for `i > dim X` — a usable bound:
it says that `dim X` is a natural number. Like the parts of that proposition, it is stated and
not proved here. -/
theorem Scheme.exists_topologicalKrullDim_le (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    ∃ d : ℕ, topologicalKrullDim X ≤ d :=
  sorry

namespace Scheme.Modules

section Vanishing

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- The cohomology of a zero sheaf of modules vanishes. -/
lemma H.subsingleton_of_isZero (hM : IsZero M) (n : ℕ) : Subsingleton (M.H n) := by
  have h : (LinearMap.id : M.H n →ₗ[Γ(X, ⊤)] M.H n) = 0 := by
    rw [← H.map_id M n, hM.eq_of_src (𝟙 M) 0, H.map_zero]
  refine ⟨fun x y ↦ ?_⟩
  have hx : ∀ z : M.H n, z = 0 := fun z ↦ by
    simpa using congrFun (congrArg DFunLike.coe h) z
  rw [hx x, hx y]

/-- **Part (4) of `prop:deg-cohomology-finiteness`**, Serre's vanishing theorem on an affine
scheme: the higher cohomology of a coherent sheaf on an affine scheme vanishes.

Stated and not proved here; this is one of the open obligations of the blueprint chapter. It
needs neither a base field nor properness, and is stated in that generality. -/
theorem H.subsingleton_of_isAffine [IsAffine X] (F : X.Modules) [F.IsCoherent] (i : ℕ)
    (hi : 0 < i) :
    Subsingleton (F.H i) :=
  sorry

end Vanishing

section BaseField

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] {M N P : X.Modules}
  {S : ShortComplex X.Modules}

section Proper

/-- **Part (1) of `prop:deg-cohomology-finiteness`**: the cohomology of a coherent sheaf on a
scheme proper over a field `k` is a finite-dimensional `k`-vector space.

Stated and not proved here; this is one of the open obligations of the blueprint chapter. Like
`AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward` of
`WeilConjectures.AlgebraicGeometry.Cohomology.Proper`, it is a `theorem` and not an `instance`,
so that every place resting on it is visible in the source. -/
theorem H.finite [IsProper (X ↘ Spec (.of k))] (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    Module.Finite k (F.H i) :=
  sorry

/-- **Part (2) of `prop:deg-cohomology-finiteness`**, Grothendieck's vanishing theorem: the
cohomology of a coherent sheaf on a scheme proper over a field vanishes in degrees exceeding
the dimension of the scheme, `dim X` being read as the topological Krull dimension of the
underlying space of `X`.

Stated and not proved here; this is one of the open obligations of the blueprint chapter. -/
theorem H.subsingleton_of_topologicalKrullDim_lt [IsProper (X ↘ Spec (.of k))] (F : X.Modules)
    [F.IsCoherent] (i : ℕ) (hi : topologicalKrullDim X < i) :
    Subsingleton (F.H i) :=
  sorry

/-- The vanishing of `H^i(X, F)` in large degrees, in the form the Euler characteristic
consumes: there is a natural number `d`, independent of the sheaf, such that `H^i(X, F) = 0`
for every coherent `F` and every `i > d`. -/
theorem H.exists_forall_subsingleton [IsProper (X ↘ Spec (.of k))] :
    ∃ d : ℕ, ∀ (F : X.Modules), F.IsCoherent → ∀ i : ℕ, d < i → Subsingleton (F.H i) := by
  obtain ⟨d, hd⟩ := Scheme.exists_topologicalKrullDim_le k X
  refine ⟨d, fun F hF i hi ↦ ?_⟩
  have := hF
  refine H.subsingleton_of_topologicalKrullDim_lt k F i (lt_of_le_of_lt hd ?_)
  exact_mod_cast hi

end Proper

/-! ### The maps of the long exact sequence as `k`-linear maps -/

/-- Functoriality of `H^n(X, -)` as a `k`-linear map, for `X` a scheme over `Spec k`. The
`Γ(X, 𝒪_X)`-linear version is `AlgebraicGeometry.Scheme.Modules.H.map`. -/
noncomputable def H.mapOver (φ : M ⟶ N) (n : ℕ) : M.H n →ₗ[k] N.H n where
  toFun x := H.map φ n x
  map_add' x y := LinearMap.map_add _ x y
  map_smul' r x := by
    rw [RingHom.id_apply, H.smul_over_def k X, H.smul_over_def k X, LinearMap.map_smul]

@[simp]
lemma H.mapOver_apply (φ : M ⟶ N) (n : ℕ) (x : M.H n) : H.mapOver k φ n x = H.map φ n x :=
  rfl

@[simp]
lemma H.mapOver_id (M : X.Modules) (n : ℕ) :
    H.mapOver k (𝟙 M) n = LinearMap.id := by
  ext x
  simp

lemma H.mapOver_comp (φ : M ⟶ N) (ψ : N ⟶ P) (n : ℕ) :
    H.mapOver k (φ ≫ ψ) n = (H.mapOver k ψ n).comp (H.mapOver k φ n) := by
  ext x
  simp [H.map_comp]

/-- An isomorphism of sheaves of modules induces a `k`-linear isomorphism on cohomology. -/
noncomputable def H.mapLinearEquivOver (e : M ≅ N) (n : ℕ) : M.H n ≃ₗ[k] N.H n :=
  LinearEquiv.ofLinearMap (H.mapOver k e.hom n) (H.mapOver k e.inv n)
    (by rw [← H.mapOver_comp, e.inv_hom_id, H.mapOver_id])
    (by rw [← H.mapOver_comp, e.hom_inv_id, H.mapOver_id])

/-- The connecting homomorphism of a short exact sequence as a `k`-linear map, for `X` a scheme
over `Spec k`. The `Γ(X, 𝒪_X)`-linear version is `AlgebraicGeometry.Scheme.Modules.H.δ`. -/
noncomputable def H.δOver (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.X₃.H n₀ →ₗ[k] S.X₁.H n₁ where
  toFun x := H.δ hS n₀ n₁ h x
  map_add' x y := LinearMap.map_add _ x y
  map_smul' r x := by
    rw [RingHom.id_apply]
    exact H.δ_smul_over k hS n₀ n₁ h r x

@[simp]
lemma H.δOver_apply (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : S.X₃.H n₀) :
    H.δOver k hS n₀ n₁ h x = H.δ hS n₀ n₁ h x :=
  rfl

/-- Exactness of the long exact cohomology sequence at `H^n(X, S.X₂)`, for the `k`-linear
maps. -/
lemma H.exact₂_over (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (H.mapOver k S.f n) (H.mapOver k S.g n) :=
  H.exact₂ hS n

/-- Exactness of the long exact cohomology sequence at `H^{n₀}(X, S.X₃)`, for the `k`-linear
maps. -/
lemma H.exact₃_over (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (H.mapOver k S.g n₀) (H.δOver k hS n₀ n₁ h) :=
  H.exact₃ hS n₀ n₁ h

/-- Exactness of the long exact cohomology sequence at `H^{n₁}(X, S.X₁)`, for the `k`-linear
maps. -/
lemma H.exact₁_over (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (H.δOver k hS n₀ n₁ h) (H.mapOver k S.f n₁) :=
  H.exact₁ hS n₀ n₁ h

/-- The long exact cohomology sequence starts with an injection. -/
lemma H.injective_mapOver_f (hS : S.ShortExact) : Function.Injective (H.mapOver k S.f 0) :=
  H.injective_map_f hS

/-! ### The Euler characteristic -/

/-- The **Euler characteristic** `χ(X, F) = ∑ i, (-1)^i dim_k H^i(X, F)` of a sheaf of modules
on a scheme `X` over a field `k`.

The sum is a `finsum`, so the definition makes sense without any finiteness hypothesis: if
`H^i(X, F)` is infinite-dimensional then `Module.finrank` is `0` there, and if infinitely many
terms are nonzero then the `finsum` is `0`. For `X` proper over `k` and `F` coherent neither
happens, and `eulerChar_eq_sum_range` rewrites `χ(X, F)` as a finite sum. -/
noncomputable def eulerChar (F : X.Modules) : ℤ :=
  ∑ᶠ i : ℕ, (-1) ^ i * (Module.finrank k (F.H i) : ℤ)

/-- If the cohomology of `F` vanishes in degrees `≥ d`, then the Euler characteristic of `F` is
the alternating sum of the first `d` dimensions. -/
lemma eulerChar_eq_sum_range (F : X.Modules) (d : ℕ)
    (hd : ∀ i : ℕ, d ≤ i → Subsingleton (F.H i)) :
    eulerChar k F = ∑ i ∈ Finset.range d, (-1) ^ i * (Module.finrank k (F.H i) : ℤ) := by
  refine finsum_eq_finsetSum_of_support_subset _ ?_
  intro i hi
  simp only [Function.mem_support, ne_eq] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  rcases lt_or_ge i d with hlt | hle
  · exact hlt
  · have := hd i hle
    exact absurd (by rw [Module.finrank_zero_of_subsingleton]; ring) hi

/-- Isomorphic sheaves of modules have the same Euler characteristic. -/
lemma eulerChar_congr (e : M ≅ N) : eulerChar k M = eulerChar k N :=
  finsum_congr fun i ↦ by rw [(H.mapLinearEquivOver k e i).finrank_eq]

/-- The Euler characteristic of a zero sheaf of modules vanishes. -/
@[simp]
lemma eulerChar_eq_zero_of_isZero (hM : IsZero M) : eulerChar k M = 0 := by
  rw [eulerChar_eq_sum_range k M 0 (fun i _ ↦ H.subsingleton_of_isZero hM i)]
  simp

section Additive

variable [IsProper (X ↘ Spec (.of k))]

/-- **`lem:deg-euler-additive`**: the Euler characteristic is additive on a short exact sequence
`0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of coherent sheaves on a scheme proper over a field.

The proof is the classical one. By `prop:deg-cohomology-finiteness`(3) — the long exact
cohomology sequence of `WeilConjectures.AlgebraicGeometry.Cohomology.LongExactSequence` — the
groups `H^i` of the three sheaves fit into a long exact sequence, which by parts (1) and (2)
consists of finite-dimensional `k`-vector spaces and has only finitely many nonzero terms. The
alternating sum of the dimensions along such a sequence vanishes; that is proved here by
rank–nullity in each degree together with a telescoping induction. -/
theorem eulerChar_add_eulerChar (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] :
    eulerChar k S.X₁ + eulerChar k S.X₃ = eulerChar k S.X₂ := by
  obtain ⟨d, hd⟩ := H.exists_forall_subsingleton k (X := X)
  have hvanish : ∀ (F : X.Modules), F.IsCoherent → ∀ i : ℕ, d + 1 ≤ i → Subsingleton (F.H i) :=
    fun F hF i hi ↦ hd F hF i hi
  -- in each degree, rank–nullity for the three maps out of `H^i(F')`, `H^i(F)` and `H^i(F'')`
  have key : ∀ i : ℕ,
      finrank k (S.X₁.H i) + finrank k (S.X₃.H i)
        = finrank k (S.X₂.H i) + finrank k (LinearMap.ker (H.mapOver k S.f i))
          + finrank k (LinearMap.range (H.δOver k hS i (i + 1) rfl)) := by
    intro i
    have h₀₁ := H.finite k S.X₁ i
    have h₀₂ := H.finite k S.X₂ i
    have h₀₃ := H.finite k S.X₃ i
    have h₁ := LinearMap.finrank_range_add_finrank_ker (H.mapOver k S.f i)
    have h₂ := LinearMap.finrank_range_add_finrank_ker (H.mapOver k S.g i)
    have h₃ := LinearMap.finrank_range_add_finrank_ker (H.δOver k hS i (i + 1) rfl)
    rw [LinearMap.exact_iff.mp (H.exact₂_over k hS i)] at h₂
    rw [LinearMap.exact_iff.mp (H.exact₃_over k hS i (i + 1) rfl)] at h₃
    omega
  -- the kernel of `H^{i+1}(F') ⟶ H^{i+1}(F)` is the image of the connecting map
  have hker : ∀ i : ℕ, finrank k (LinearMap.ker (H.mapOver k S.f (i + 1)))
      = finrank k (LinearMap.range (H.δOver k hS i (i + 1) rfl)) := fun i ↦ by
    rw [LinearMap.exact_iff.mp (H.exact₁_over k hS i (i + 1) rfl)]
  -- `H^0(F') ⟶ H^0(F)` is injective
  have hker₀ : finrank k (LinearMap.ker (H.mapOver k S.f 0)) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr (H.injective_mapOver_f k hS)]
    simp
  -- the kernel vanishes above the dimension of `X`
  have hkertop : finrank k (LinearMap.ker (H.mapOver k S.f (d + 1))) = 0 := by
    have hsub : Subsingleton (S.X₁.H (d + 1)) := hvanish S.X₁ inferInstance _ le_rfl
    exact Module.finrank_zero_of_subsingleton
  -- the telescoping identity for the alternating sum
  have tele : ∀ (κ γ : ℕ → ℕ), κ 0 = 0 → (∀ i, κ (i + 1) = γ i) → ∀ m : ℕ,
      ∑ i ∈ Finset.range m, ((-1 : ℤ) ^ i * ((κ i : ℤ) + (γ i : ℤ)))
        = -((-1 : ℤ) ^ m * (κ m : ℤ)) := by
    intro κ γ hκ hγ m
    induction m with
    | zero => simp [hκ]
    | succ m ih => rw [Finset.sum_range_succ, ih, hγ m, pow_succ]; ring
  rw [eulerChar_eq_sum_range k S.X₁ (d + 1) (hvanish _ inferInstance),
    eulerChar_eq_sum_range k S.X₂ (d + 1) (hvanish _ inferInstance),
    eulerChar_eq_sum_range k S.X₃ (d + 1) (hvanish _ inferInstance),
    ← sub_eq_zero, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range (d + 1),
      ((-1 : ℤ) ^ i * (finrank k (S.X₁.H i) : ℤ) + (-1 : ℤ) ^ i * (finrank k (S.X₃.H i) : ℤ)
        - (-1 : ℤ) ^ i * (finrank k (S.X₂.H i) : ℤ))
      = (-1 : ℤ) ^ i * ((finrank k (LinearMap.ker (H.mapOver k S.f i)) : ℤ)
        + (finrank k (LinearMap.range (H.δOver k hS i (i + 1) rfl)) : ℤ)) := by
    intro i _
    have hz : (finrank k (S.X₁.H i) : ℤ) + (finrank k (S.X₃.H i) : ℤ)
        = (finrank k (S.X₂.H i) : ℤ) + (finrank k (LinearMap.ker (H.mapOver k S.f i)) : ℤ)
          + (finrank k (LinearMap.range (H.δOver k hS i (i + 1) rfl)) : ℤ) := by
      exact_mod_cast key i
    linear_combination ((-1 : ℤ) ^ i) * hz
  rw [Finset.sum_congr rfl hterm,
    tele (fun i ↦ finrank k (LinearMap.ker (H.mapOver k S.f i)))
      (fun i ↦ finrank k (LinearMap.range (H.δOver k hS i (i + 1) rfl))) hker₀ hker (d + 1),
    hkertop]
  simp

end Additive

/-! ### The Euler characteristic on an affine scheme -/

section Affine

variable [IsAffine X]

/-- **`lem:deg-euler-affine`**: on an affine scheme the Euler characteristic of a coherent sheaf
is the dimension of its space of global sections, all higher cohomology vanishing.

The space of global sections is written here as `H^0(X, F)`; it is identified with `Γ(X, F)`
by `AlgebraicGeometry.Scheme.Modules.H.linearEquiv₀`. -/
theorem eulerChar_eq_finrank_H_zero (F : X.Modules) [F.IsCoherent] :
    eulerChar k F = finrank k (F.H 0) := by
  rw [eulerChar_eq_sum_range k F 1 (fun i hi ↦ H.subsingleton_of_isAffine F i hi)]
  simp

/-- **`lem:deg-euler-affine`**, second half: the Euler characteristic of the structure sheaf of
a nonempty affine scheme proper over `k` is positive. Indeed it is `dim_k Γ(X, 𝒪_X)`, and
`Γ(X, 𝒪_X)` is a nonzero `k`-vector space. -/
theorem eulerChar_unit_pos [IsProper (X ↘ Spec (.of k))] [Nonempty X] :
    0 < eulerChar k (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  have hne : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have hΓ : Nontrivial Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) :=
    inferInstanceAs (Nontrivial Γ(X, ⊤))
  have hnt : Nontrivial (H (X := X) (SheafOfModules.unit X.ringCatSheaf) 0) :=
    (H.linearEquiv₀ (X := X) (SheafOfModules.unit X.ringCatSheaf)).toEquiv.nontrivial
  have hfin := H.finite k (X := X) (SheafOfModules.unit X.ringCatSheaf) 0
  rw [eulerChar_eq_finrank_H_zero]
  exact_mod_cast Module.finrank_pos (R := k)

end Affine

/-! ### The Euler characteristic along a finite morphism -/

section FiniteMorphism

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))] (f : X ⟶ Y)

/-- **`prop:deg-euler-finite-morphism`(1)**, first half: the direct image of a coherent sheaf
along a finite morphism is coherent.

Stated and not proved here; this is one of the open obligations of the blueprint chapter. The
proper case over a locally Noetherian base is
`AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward` in
`WeilConjectures.AlgebraicGeometry.Cohomology.Proper`; neither implies the other, since a
finite morphism is proper but no Noetherian hypothesis is made here. -/
theorem isCoherent_pushforward_of_isFinite [IsFinite f] (F : X.Modules) [F.IsCoherent] :
    ((pushforward f).obj F).IsCoherent :=
  sorry

/-- **`prop:deg-euler-finite-morphism`(1)**, second half: the cohomology of a coherent sheaf is
unchanged by the direct image along a finite morphism. A finite morphism is affine, so the
higher direct images vanish and the Leray spectral sequence degenerates.

Stated and not proved here; this is one of the open obligations of the blueprint chapter. -/
noncomputable def H.pushforwardLinearEquiv [IsFinite f] [f.IsOver (Spec (.of k))]
    (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    F.H i ≃ₗ[k] ((pushforward f).obj F).H i :=
  sorry

/-- **`prop:deg-euler-finite-morphism`(1)**: the Euler characteristic is unchanged by the direct
image along a finite morphism. This is a consequence of `H.pushforwardLinearEquiv`. -/
theorem eulerChar_pushforward [IsFinite f] [f.IsOver (Spec (.of k))] (F : X.Modules)
    [F.IsCoherent] :
    eulerChar k ((pushforward f).obj F) = eulerChar k F :=
  finsum_congr fun i ↦ by rw [(H.pushforwardLinearEquiv k f F i).finrank_eq]

end FiniteMorphism

end BaseField

/-! ### The projection formula -/

section ProjectionFormula

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`prop:deg-euler-finite-morphism`(2)**, the **projection formula**: for `F` a sheaf of
modules on `X` and `N` a locally free sheaf of finite rank on `Y`, the direct image of
`F ⊗ f^*N` is `(f_*F) ⊗ N`.

Stated and not proved here; this is one of the open obligations of the blueprint chapter — it
is the projection formula of notion (N5) of the chapter on the theorem of the cube. Its
naturality in `F` and in `N` is `pushforwardTensorPullbackIso_naturality_left` and
`pushforwardTensorPullbackIso_naturality_right`. No base field is involved. -/
noncomputable def pushforwardTensorPullbackIso [IsFinite f] (F : X.Modules) (N : Y.Modules)
    [N.IsLocallyFree] [N.IsFiniteType] :
    (pushforward f).obj (F ⊗ (pullback f).obj N) ≅ (pushforward f).obj F ⊗ N :=
  sorry

/-- The projection formula is natural in the sheaf on the source.

Stated and not proved here, together with `pushforwardTensorPullbackIso`. -/
lemma pushforwardTensorPullbackIso_naturality_left [IsFinite f] {F F' : X.Modules} (φ : F ⟶ F')
    (N : Y.Modules) [N.IsLocallyFree] [N.IsFiniteType] :
    (pushforward f).map (φ ▷ (pullback f).obj N) ≫ (pushforwardTensorPullbackIso f F' N).hom
      = (pushforwardTensorPullbackIso f F N).hom ≫ ((pushforward f).map φ ▷ N) :=
  sorry

/-- The projection formula is natural in the sheaf on the target.

Stated and not proved here, together with `pushforwardTensorPullbackIso`. -/
lemma pushforwardTensorPullbackIso_naturality_right [IsFinite f] (F : X.Modules)
    {N N' : Y.Modules} [N.IsLocallyFree] [N.IsFiniteType] [N'.IsLocallyFree] [N'.IsFiniteType]
    (ψ : N ⟶ N') :
    (pushforward f).map (F ◁ (pullback f).map ψ) ≫ (pushforwardTensorPullbackIso f F N').hom
      = (pushforwardTensorPullbackIso f F N).hom ≫ ((pushforward f).obj F ◁ ψ) :=
  sorry

end ProjectionFormula

end Scheme.Modules

end AlgebraicGeometry
