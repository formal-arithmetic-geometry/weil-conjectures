/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.AffineComplement
public import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SegreTwist
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Ample invertible modules and the Hilbert degree

An `𝒪_X`-module is *very ample* relative to `f : X ⟶ S` if it is the pullback of `𝒪(1)` along
a closed immersion of `X` into a projective space `ℙ(n; S)` over `S`; it is then invertible. An
invertible module on a `K`-scheme is *ample* if some positive tensor power of it is very ample;
since very ample modules come from *closed* immersions into projective space, this is ampleness
on a projective `K`-scheme (see the warning in the docstring of `AlgebraicGeometry.IsAmple`).
For an ample invertible module `M` on a proper `K`-scheme `X` of dimension `g`, the function
`m ↦ χ(X, M^{⊗ m})` is a numerical polynomial of degree at most `g`, and the *degree of `X` with
respect to `M`* is `g!` times its leading coefficient.

`AlgebraicGeometry.IsVeryAmple` and `AlgebraicGeometry.IsAmple` are built on the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist`. The degree `AlgebraicGeometry.Scheme.Hom.degree` is
the `g`-th forward difference `fwdDiff` at `0` of the Hilbert function `m ↦ χ(X, M^{⊗ m})`, with
the Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar`; it is `g!` times the
leading coefficient whenever that function is a numerical polynomial of degree at most `g`
(`Polynomial.fwdDiff_iter_degree_eq_factorial`).

## Main definitions

- `AlgebraicGeometry.IsVeryAmple`, `AlgebraicGeometry.IsAmple`: very ample and ample modules.
- `AlgebraicGeometry.Scheme.Hom.hilbertFunction`: the Hilbert function `m ↦ χ(X, M^{⊗ m})`.
- `AlgebraicGeometry.Scheme.Hom.degree`: the degree of a proper scheme with respect to an ample
  invertible module.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_polynomial_hilbertFunction`: the Hilbert function of an
  ample invertible module on a proper scheme is a polynomial of degree at most `dim X`.
- `AlgebraicGeometry.Scheme.Hom.degree_eq_factorial_mul_coeff`: the degree is `g!` times the
  coefficient of `m^g` of the Hilbert polynomial.
- `AlgebraicGeometry.Scheme.Hom.degree_tensorPow`: `deg_{M^{⊗ k}}(X) = k^g deg_M(X)`.
- `AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple_of_nonempty`: an ample invertible module
  on a nonempty proper scheme has positive degree.
- `AlgebraicGeometry.Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one`: in dimension
  one the degree is the cohomological degree `χ(M) - χ(𝒪_X)`.
- `AlgebraicGeometry.IsVeryAmple.isInvertible`: a very ample module is invertible.
- `AlgebraicGeometry.Scheme.Modules.finiteDimensional_H`: the cohomology of an invertible module
  on a proper scheme over a field is finite-dimensional.
- `AlgebraicGeometry.Scheme.Modules.degree_eq_sum_of_pairwise_disjoint`: the degree is additive
  over a finite disjoint union of open subschemes.
- `AlgebraicGeometry.Scheme.Modules.degree_eq_zero_of_topologicalKrullDim_le_zero`: an
  invertible module on a connected noetherian scheme of dimension `0` has degree `0`.
- `AlgebraicGeometry.IsAmple.pullback`: the restriction of an ample module to a closed subscheme
  is ample.
- `AlgebraicGeometry.IsAmple.pullback_of_field` and `AlgebraicGeometry.IsVeryAmple.of_pullback`:
  ampleness is stable under field extension, and very ampleness descends along it.
- `AlgebraicGeometry.isAffine_compl_of_isAmple_dual_toModules`: the complement of an effective
  Cartier divisor with ample line bundle is affine.
- `AlgebraicGeometry.IsAmple.tensorPow`: positive tensor powers of an ample module are ample.
- `AlgebraicGeometry.IsVeryAmple.tensorObj`, `AlgebraicGeometry.IsAmple.tensorObj`: tensor
  products of very ample, respectively ample, modules are very ample, respectively ample.
- `AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple_of_connectedSpace`: an ample invertible
  module on a connected proper curve has positive degree.
- `AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple`: an ample invertible module on a proper
  curve has positive degree.
- `AlgebraicGeometry.IsAmple.isEmpty_iso_unit`: an ample invertible module on a proper curve is
  not trivial.
- `AlgebraicGeometry.IsAmple.isEmpty_tensorPow_iso_unit`: no positive tensor power of an ample
  invertible module on a proper curve is trivial.
- `AlgebraicGeometry.Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow`: twisting the
  Hilbert function by a coherent module of generic rank `r` multiplies the degree by `r`.
- `AlgebraicGeometry.Scheme.Hom.degree_pullback`: the degree multiplies by the degree of the
  morphism under pullback along a finite surjective morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Function MonoidalCategory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

An `𝒪_X`-module `M` is *very ample* relative to `f : X ⟶ S` if there is a closed immersion
`i : X ⟶ ℙ(n; S)` over `S`, into a projective space with finitely many homogeneous
coordinates, with `i^* 𝒪(1) ≅ M`.

This is the "projective" variant of the notion: Hartshorne (II.5) and EGA II (4.4.2) only ask
for an immersion. The two agree when `f` is proper, since an immersion from a proper
`S`-scheme into the separated `S`-scheme `ℙ(n; S)` is closed, and every use of very ample
modules in the project is for a proper `f`. -/
def IsVeryAmple {S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) : Prop :=
  ∃ (n : Type u) (i : X ⟶ ℙ(n; S)), Finite n ∧ IsClosedImmersion i ∧ i ≫ ℙ(n; S) ↘ S = f ∧
    Nonempty (ProjectiveSpace.twistRestrict i 1 ≅ M)

/-- **A very ample module is invertible**, being the pullback of the invertible module
`𝒪(1)`. -/
lemma IsVeryAmple.isInvertible {S : Scheme.{u}} {f : X ⟶ S} {M : X.Modules}
    (h : IsVeryAmple f M) : M.IsInvertible := by
  obtain ⟨n, i, -, -, -, ⟨e⟩⟩ := h
  exact Scheme.Modules.IsInvertible.of_iso e

/-- Very ampleness only depends on the isomorphism class of the module. -/
lemma IsVeryAmple.of_iso {S : Scheme.{u}} {f : X ⟶ S} {M N : X.Modules} (h : IsVeryAmple f M)
    (e : M ≅ N) : IsVeryAmple f N := by
  obtain ⟨n, i, hn, hi, hif, ⟨e'⟩⟩ := h
  exact ⟨n, i, hn, hi, hif, ⟨e' ≪≫ e⟩⟩

/-- **The restriction of a very ample module to a closed subscheme is very ample**: if `M` is
the pullback of `𝒪(1)` along a closed immersion `i`, then `g^* M` is its pullback along the
closed immersion `g ≫ i`. -/
lemma IsVeryAmple.pullback {S Z : Scheme.{u}} {f : X ⟶ S} {M : X.Modules} (h : IsVeryAmple f M)
    (g : Z ⟶ X) [IsClosedImmersion g] :
    IsVeryAmple (g ≫ f) ((Scheme.Modules.pullback g).obj M) := by
  obtain ⟨n, i, hn, hi, hif, ⟨e⟩⟩ := h
  exact ⟨n, g ≫ i, hn, inferInstance, by rw [Category.assoc, hif],
    ⟨(Scheme.Modules.pullbackComp g i).symm.app _ ≪≫ (Scheme.Modules.pullback g).mapIso e⟩⟩

/-- Blueprint `lem-chow-segre`: The Segre embedding is a closed immersion (the consequence that
`𝒪(1) ⊠ 𝒪(1)` is very ample, recorded in its detailed form).

**A tensor product of very ample modules is very ample.** If `M = i^* 𝒪(1)` and `N = j^* 𝒪(1)`
for closed immersions `i : X ⟶ ℙ(n; S)` and `j : X ⟶ ℙ(m; S)` over `S`, then `M ⊗ N` is the
pullback of `𝒪(1)` along the composite of the closed immersion `(i, j)` into
`ℙ(n; S) ×_S ℙ(m; S)` with the Segre embedding into `ℙ(n × m; S)`. -/
theorem IsVeryAmple.tensorObj {S : Scheme.{u}} {f : X ⟶ S} {M N : X.Modules}
    (hM : IsVeryAmple f M) (hN : IsVeryAmple f N) : IsVeryAmple f (M ⊗ N) := by
  obtain ⟨n, i, hn, hi, hif, ⟨e⟩⟩ := hM
  obtain ⟨m, j, hm, hj, hjf, ⟨e'⟩⟩ := hN
  let k : X ⟶ Limits.pullback (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) := pullback.lift i j (hif.trans hjf.symm)
  have : IsClosedImmersion (k ≫ pullback.fst _ _) := by rwa [pullback.lift_fst]
  have : IsClosedImmersion k := IsClosedImmersion.of_comp k (pullback.fst _ _)
  obtain ⟨t⟩ := ProjectiveSpace.nonempty_twistRestrict_segre_iso n m S
  obtain ⟨u⟩ := Scheme.Modules.nonempty_pullback_tensorObj_iso k
    (ProjectiveSpace.twistRestrict (pullback.fst (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)) 1)
    (ProjectiveSpace.twistRestrict (pullback.snd (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)) 1)
  refine ⟨n × m, k ≫ ProjectiveSpace.segre n m S, inferInstance, inferInstance,
    by simp [k, hif], ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp k _).symm.app _ ≪≫ (Scheme.Modules.pullback k).mapIso t ≪≫
    u ≪≫ (((Scheme.Modules.pullbackComp k _).app _ ≪≫
        (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _)).app _ ≪≫ e) ⊗ᵢ
      ((Scheme.Modules.pullbackComp k _).app _ ≪≫
        (Scheme.Modules.pullbackCongr (pullback.lift_snd _ _ _)).app _ ≪≫ e'))

/-- **Positive tensor powers of a very ample module are very ample**, by
`AlgebraicGeometry.IsVeryAmple.tensorObj`. -/
theorem IsVeryAmple.tensorPow {S : Scheme.{u}} {f : X ⟶ S} {M : X.Modules}
    (hM : IsVeryAmple f M) : ∀ {k : ℕ}, 0 < k → IsVeryAmple f (M.tensorPow k)
  | 1, _ => hM.of_iso (ρ_ M).symm
  | k + 2, _ => hM.tensorObj (hM.tensorPow (Nat.succ_pos k))

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

An `𝒪_X`-module `M` on a `K`-scheme `X` is *ample* if it is invertible and some positive tensor
power of it is very ample in the sense of `AlgebraicGeometry.IsVeryAmple`.

**Warning.** `AlgebraicGeometry.IsVeryAmple` asks for a *closed* immersion into a projective
space, so `IsAmple f M` means "`M` is ample and `X` is projective over `K`". It is the standard
notion (EGA II 4.5.3, Stacks `01PS`) when `f` is proper, which is the only case in which the
blueprint uses it, but an ample module on a non-proper `K`-scheme, such as `𝒪` on `𝔸¹_K`, does
not satisfy `IsAmple`. Statements such as Serre vanishing
(`AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensorObj_tensorPow`) hold without a
properness hypothesis for this reason. -/
def IsAmple (f : X ⟶ Spec (.of K)) (M : X.Modules) : Prop :=
  M.IsInvertible ∧ ∃ m : ℕ, 0 < m ∧ IsVeryAmple f (M.tensorPow m)

/-- An ample module is invertible. -/
lemma IsAmple.isInvertible {f : X ⟶ Spec (.of K)} {M : X.Modules} (h : IsAmple f M) :
    M.IsInvertible :=
  h.1

/-- The Hilbert function `m ↦ χ(X, M^{⊗ m})` of an `𝒪_X`-module `M` on a `K`-scheme `X`, with
the Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar` over `K`. -/
noncomputable def Scheme.Hom.hilbertFunction (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℕ → ℤ :=
  letI : X.Over (Spec (.of K)) := ⟨f⟩
  fun m ↦ Scheme.Modules.eulerChar K (M.tensorPow m)

open scoped fwdDiff in
/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

The degree of a `K`-scheme `X` of dimension `g` with respect to an `𝒪_X`-module `M`: the `g`-th
forward difference at `0` of the Hilbert function `m ↦ χ(X, M^{⊗ m})`. When the Hilbert
function is a numerical polynomial of degree at most `g`, as it is for `X` proper and `M` ample
invertible, this equals `g!` times its coefficient of `m^g`. Here `g` is the topological Krull
dimension of `X`, read as `0` if `X` is empty or infinite-dimensional.

The value is meaningful only for `f` proper and `M` coherent: otherwise the Euler
characteristics involved may be junk values. -/
noncomputable def Scheme.Hom.degree (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℤ :=
  Δ_[1]^[((topologicalKrullDim X).unbotD 0).toNat] (f.hilbertFunction M) 0

/-- The degree as an explicit alternating sum of Euler characteristics:
`∑_{i=0}^{g} (-1)^(g-i) (g choose i) χ(X, M^{⊗ i})`. -/
lemma Scheme.Hom.degree_eq_sum (f : X ⟶ Spec (.of K)) (M : X.Modules) :
    f.degree M = ∑ i ∈ Finset.range (((topologicalKrullDim X).unbotD 0).toNat + 1),
      ((-1 : ℤ) ^ (((topologicalKrullDim X).unbotD 0).toNat - i) *
        (((topologicalKrullDim X).unbotD 0).toNat.choose i : ℤ)) • f.hilbertFunction M i := by
  rw [degree, fwdDiff_iter_eq_sum_shift]
  simp

/-- On a `K`-scheme of dimension one, the degree with respect to `M` is the cohomological
degree `χ(M) - χ(𝒪_X)` of `AlgebraicGeometry.Scheme.Modules.degree`. -/
lemma Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one (f : X ⟶ Spec (.of K))
    (h : topologicalKrullDim X = 1) (M : X.Modules) :
    letI : X.Over (Spec (.of K)) := ⟨f⟩
    f.degree M = Scheme.Modules.degree K M := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have hg : ((topologicalKrullDim X).unbotD 0).toNat = 1 := by
    rw [h]
    rfl
  rw [degree, hg, Function.iterate_one, fwdDiff, zero_add, Scheme.Modules.degree]
  simp only [hilbertFunction, Scheme.Modules.tensorPow_zero]
  rw [Scheme.Modules.tensorPow_succ, Scheme.Modules.tensorPow_zero,
    Scheme.Modules.eulerChar_congr K (MonoidalCategory.rightUnitor M)]
  rfl

/-- Blueprint `lem-sc-hilbert-polynomial`: The Hilbert polynomial.

Let `X` be a proper scheme of dimension `g` over a field `K` and `M` an ample invertible
`𝒪_X`-module. Then `m ↦ χ(X, M^{⊗ m})` is a numerical polynomial of degree at most `g`: there is
a polynomial `P` over `ℚ` of degree at most `g` with `P(m) = χ(X, M^{⊗ m})` for all `m`, the
*Hilbert polynomial* of `M` (Stacks, Tag 0BEM). -/
theorem Scheme.Hom.exists_polynomial_hilbertFunction (f : X ⟶ Spec (.of K)) [IsProper f]
    (M : X.Modules) (hM : IsAmple f M) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ ((topologicalKrullDim X).unbotD 0).toNat ∧
      ∀ m : ℕ, P.eval (m : ℚ) = f.hilbertFunction M m :=
  sorry

open scoped fwdDiff in
/-- Blueprint `def-sc-hilbert-degree`: The Hilbert degree of an ample line bundle.

If the Hilbert function `m ↦ χ(X, M^{⊗ m})` is given by a polynomial `P` of degree at most
`g = dim X`, then the degree of `X` with respect to `M` is `g!` times the coefficient of `m^g`
in `P`. -/
theorem Scheme.Hom.degree_eq_factorial_mul_coeff (f : X ⟶ Spec (.of K)) (M : X.Modules)
    {P : Polynomial ℚ} (hP : P.natDegree ≤ ((topologicalKrullDim X).unbotD 0).toNat)
    (hPM : ∀ m : ℕ, P.eval (m : ℚ) = f.hilbertFunction M m) :
    (f.degree M : ℚ) = ((topologicalKrullDim X).unbotD 0).toNat.factorial *
      P.coeff ((topologicalKrullDim X).unbotD 0).toNat := by
  rw [degree]
  generalize ((topologicalKrullDim X).unbotD 0).toNat = g at hP ⊢
  have h : ((Δ_[1]^[g] (f.hilbertFunction M) 0 : ℤ) : ℚ) = Δ_[1]^[g] P.eval 0 := by
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [← hPM]
  rw [h]
  rcases hP.lt_or_eq with hlt | rfl
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    simp
  · rw [Polynomial.fwdDiff_iter_degree_eq_factorial]
    simp [mul_comm]

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

Let `X` be a proper scheme of dimension `g` over a field `K` and `M` an ample invertible
`𝒪_X`-module. Then `m ↦ χ(X, M^{⊗ m})` is given by a polynomial `P` of degree at most `g`, and
the degree of `X` with respect to `M` is `g!` times the leading coefficient of `P`, its
coefficient of `m^g`. -/
theorem Scheme.Hom.exists_polynomial_degree_eq_factorial_mul_coeff (f : X ⟶ Spec (.of K))
    [IsProper f] (M : X.Modules) (hM : IsAmple f M) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ ((topologicalKrullDim X).unbotD 0).toNat ∧
      (∀ m : ℕ, P.eval (m : ℚ) = f.hilbertFunction M m) ∧
      (f.degree M : ℚ) = ((topologicalKrullDim X).unbotD 0).toNat.factorial *
        P.coeff ((topologicalKrullDim X).unbotD 0).toNat := by
  obtain ⟨P, hP, hPM⟩ := f.exists_polynomial_hilbertFunction M hM
  exact ⟨P, hP, hPM, f.degree_eq_factorial_mul_coeff M hP hPM⟩

/-- The Hilbert function only depends on the isomorphism class of the module. -/
lemma Scheme.Hom.hilbertFunction_congr (f : X ⟶ Spec (.of K)) {M N : X.Modules} (e : M ≅ N) :
    f.hilbertFunction M = f.hilbertFunction N := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have h (m : ℕ) : Nonempty (M.tensorPow m ≅ N.tensorPow m) := by
    induction m with
    | zero => exact ⟨Iso.refl _⟩
    | succ m ih => exact ⟨e ⊗ᵢ ih.some⟩
  funext m
  exact Scheme.Modules.eulerChar_congr K (h m).some

/-- The degree only depends on the isomorphism class of the module. -/
lemma Scheme.Hom.degree_congr (f : X ⟶ Spec (.of K)) {M N : X.Modules} (e : M ≅ N) :
    f.degree M = f.degree N := by
  rw [degree, degree, f.hilbertFunction_congr e]

/-- The Hilbert function of `M^{⊗ k}` is `m ↦ χ(X, M^{⊗ k m})`. -/
lemma Scheme.Hom.hilbertFunction_tensorPow (f : X ⟶ Spec (.of K)) (M : X.Modules) (k m : ℕ) :
    f.hilbertFunction (M.tensorPow k) m = f.hilbertFunction M (k * m) := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  exact Scheme.Modules.eulerChar_congr K (M.tensorPowMulIso k m).symm

/-- **The degree of a tensor power.** Let `X` be a proper scheme of dimension `g` over `K` and
`M` an ample invertible `𝒪_X`-module. Then `deg_{M^{⊗ k}}(X) = k^g deg_M(X)`: if `P` is the
Hilbert polynomial of `M`, then `m ↦ χ(X, M^{⊗ k m})` is given by the polynomial `P(k X)`, whose
coefficient of `m^g` is `k^g` times that of `P`.

This is a step of the proof of blueprint `sk-prop-av-isogeny`. -/
theorem Scheme.Hom.degree_tensorPow (f : X ⟶ Spec (.of K)) [IsProper f] (M : X.Modules)
    (hM : IsAmple f M) (k : ℕ) :
    f.degree (M.tensorPow k) = k ^ ((topologicalKrullDim X).unbotD 0).toNat * f.degree M := by
  have hcoeff (P : Polynomial ℚ) (n : ℕ) :
      (P.comp (Polynomial.C (k : ℚ) * Polynomial.X)).coeff n = (k : ℚ) ^ n * P.coeff n := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
    | monomial m a =>
      simp only [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
        ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
      split_ifs with h₁ h₂ h₂
      · subst h₁; ring
      · exact absurd h₁.symm h₂
      · exact absurd h₂.symm h₁
      · simp
  obtain ⟨P, hP, hPM, hdeg⟩ := f.exists_polynomial_degree_eq_factorial_mul_coeff M hM
  set g := ((topologicalKrullDim X).unbotD 0).toNat
  have hQ : (P.comp (Polynomial.C (k : ℚ) * Polynomial.X)).natDegree ≤ g :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun n hn ↦ by
      rw [hcoeff, Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_lt hn), mul_zero]
  have hQM (m : ℕ) : (P.comp (Polynomial.C (k : ℚ) * Polynomial.X)).eval (m : ℚ) =
      f.hilbertFunction (M.tensorPow k) m := by
    rw [f.hilbertFunction_tensorPow, ← hPM]
    simp
  have := f.degree_eq_factorial_mul_coeff (M.tensorPow k) hQ hQM
  rw [hcoeff] at this
  have h : (f.degree (M.tensorPow k) : ℚ) = (k : ℚ) ^ g * f.degree M := by
    rw [this, hdeg]
    ring
  exact_mod_cast h

namespace Scheme.Modules

section Additivity

variable (K) [X.Over (Spec (.of K))]

/-- **Finiteness of cohomology.** The cohomology of an invertible module on a proper scheme over
a field `K` is finite-dimensional over `K`. This is a special case of the finiteness theorem
for the cohomology of coherent modules on proper schemes (EGA III, 3.2.1),
`AlgebraicGeometry.Scheme.Modules.finiteDimensional_H_of_isProper`, since an invertible module
is locally free of rank one, hence of finite presentation.

For `M = 𝒪_X` on a curve, this is the finiteness of the genus `dim_k H¹(X, 𝒪_X)`
(blueprint `lem-pc-genus-well-defined`). This is used in the proof of blueprint
`lem-sc-ample-positive-degree`. -/
instance finiteDimensional_H [IsProper (X ↘ Spec (.of K))] (M : X.Modules) [M.IsInvertible]
    (q : ℕ) : FiniteDimensional K (M.H q) :=
  have := IsInvertible.sheafOfModules_isInvertible M
  finiteDimensional_H_of_isProper M q

/-- **The degree is additive over a finite disjoint union.** If a noetherian scheme `X` of
finite dimension is the disjoint union of finitely many open subschemes `U i`, then
`deg M = ∑ᵢ deg (M|_{U i})`, provided the cohomology of `M` and `𝒪_X` is finite-dimensional. -/
theorem degree_eq_sum_of_pairwise_disjoint [IsNoetherian X] {n : ℕ}
    (hn : topologicalKrullDim X ≤ n) {ι : Type*}
    [Fintype ι] (U : ι → X.Opens) (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤)
    (M : X.Modules) [∀ q, FiniteDimensional K (M.H q)]
    [∀ q, FiniteDimensional K ((𝟙_ X.Modules).H q)] :
    M.degree K = ∑ i,
      letI : (U i).toScheme.Over (Spec (.of K)) := ⟨(U i).ι ≫ X ↘ Spec (.of K)⟩
      ((Scheme.Modules.pullback (U i).ι).obj M).degree K := by
  let (i : ι) : (U i).toScheme.Over (Spec (.of K)) := ⟨(U i).ι ≫ X ↘ Spec (.of K)⟩
  simp only [degree, Finset.sum_sub_distrib]
  rw [eulerChar_eq_sum_of_pairwise_disjoint K hn U hU hcover M]
  congr 1
  exact (eulerChar_eq_sum_of_pairwise_disjoint K hn U hU hcover (𝟙_ X.Modules)).trans
    (Finset.sum_congr rfl fun i _ ↦ eulerChar_congr K (pullbackObjUnitIso _))

/-- On a connected locally noetherian `K`-scheme of dimension `0`, every invertible module has
degree `0`: the scheme is artinian, hence discrete, hence a single point, on which every
invertible module is trivial. -/
theorem degree_eq_zero_of_topologicalKrullDim_le_zero [IsLocallyNoetherian X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X ≤ 0) (L : X.Modules) [L.IsInvertible] : L.degree K = 0 := by
  have := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  have : Subsingleton X := Set.subsingleton_univ_iff.mp isPreconnected_univ.subsingleton
  obtain ⟨e⟩ := IsInvertible.nonempty_iso_unit (Classical.arbitrary X) L
  rw [degree_congr K e, degree_unit]

end Additivity

end Scheme.Modules

/-- **The restriction of an ample module to a closed subscheme is ample.** If `L^{⊗ n}` is the
pullback of `𝒪(1)` along a closed immersion `X ⟶ ℙ(m; K)`, then `(i^* L)^{⊗ n} ≅ i^* (L^{⊗ n})`
is its pullback along the closed immersion `Z ⟶ X ⟶ ℙ(m; K)` (Stacks, Properties of Schemes,
Section 28.26).

This is used in the proof of blueprint `lem-sc-ample-positive-degree`. -/
theorem IsAmple.pullback {Z : Scheme.{u}} {f : X ⟶ Spec (.of K)} {L : X.Modules}
    (hL : IsAmple f L) (i : Z ⟶ X) [IsClosedImmersion i] :
    IsAmple (i ≫ f) ((Scheme.Modules.pullback i).obj L) := by
  obtain ⟨hinv, m, hm, h⟩ := hL
  exact ⟨inferInstance, m, hm, (h.pullback i).of_iso
    (Scheme.Modules.nonempty_pullback_tensorPow_iso i L m).some⟩

/-- **Positive tensor powers of an ample module are ample.** If `L^{⊗ m}` is very ample, then
so is `(L^{⊗ m})^{⊗ k}` (`AlgebraicGeometry.IsVeryAmple.tensorPow`, via the Segre embedding), and
`(L^{⊗ m})^{⊗ k} ≅ L^{⊗ mk} ≅ (L^{⊗ k})^{⊗ m}`.

This is used in the proof of blueprint `lem-sc-mult-n-finite-kernel`. -/
theorem IsAmple.tensorPow {f : X ⟶ Spec (.of K)} {L : X.Modules} (hL : IsAmple f L) {k : ℕ}
    (hk : 0 < k) : IsAmple f (L.tensorPow k) := by
  obtain ⟨hinv, m, hm, hLm⟩ := hL
  exact ⟨inferInstance, m, hm, (hLm.tensorPow hk).of_iso ((L.tensorPowMulIso m k).symm ≪≫
    eqToIso (congrArg L.tensorPow (Nat.mul_comm m k)) ≪≫ L.tensorPowMulIso k m)⟩

/-- Blueprint `lem-sc-ample-tensor`: Tensor products of ample modules.

**A tensor product of ample modules is ample** (Stacks 0890). If `L^{⊗ a}` and `M^{⊗ b}` are
very ample, then so are `(L^{⊗ a})^{⊗ b} ≅ L^{⊗ ab}` and `(M^{⊗ b})^{⊗ a} ≅ M^{⊗ ab}`, hence also
their tensor product `(L ⊗ M)^{⊗ ab}`, by the Segre embedding
(`AlgebraicGeometry.IsVeryAmple.tensorObj`). -/
theorem IsAmple.tensorObj {f : X ⟶ Spec (.of K)} {L M : X.Modules} (hL : IsAmple f L)
    (hM : IsAmple f M) : IsAmple f (L ⊗ M) := by
  obtain ⟨hinvL, a, ha, hLa⟩ := hL
  obtain ⟨hinvM, b, hb, hMb⟩ := hM
  refine ⟨inferInstance, a * b, Nat.mul_pos ha hb,
    ((hLa.tensorPow hb).tensorObj (hMb.tensorPow ha)).of_iso ?_⟩
  exact ((L.tensorPowMulIso a b).symm ⊗ᵢ ((M.tensorPowMulIso b a).symm ≪≫
    eqToIso (congrArg M.tensorPow (Nat.mul_comm b a)))) ≪≫ (L.tensorPowTensorObjIso M _).symm

/-- **Very ampleness is stable under field extension.** If `M = i^* 𝒪(1)` for a closed
immersion `i : X ⟶ ℙ(n; k)`, then for a field extension `K/k` the base change `M_K` is the
pullback of `𝒪(1)` along the base change `i_K : X_K ⟶ ℙ(n; K)` of `i`, which is again a closed
immersion (Stacks 01JY).

(blueprint: `lem-pc-very-ample-ample`, `lem-pc-closed-imm-base-change`) -/
theorem IsVeryAmple.pullback_of_field {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}
    {M : X.Modules} (h : IsVeryAmple f M) (K : Type u) [Field K] [Algebra k K] :
    IsVeryAmple (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M) := by
  obtain ⟨n, i, hn, hi, hif, ⟨e⟩⟩ := h
  set g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have w : pullback.snd f g ≫ g = (pullback.fst f g ≫ i) ≫ ℙ(n; Spec (.of k)) ↘ Spec (.of k) := by
    rw [Category.assoc, hif, pullback.condition]
  let i' := ProjectiveSpace.liftBaseChange (pullback.snd f g) (pullback.fst f g ≫ i) w
  -- `i'` is the base change of `i` along `ℙ(n; K) ⟶ ℙ(n; k)`.
  have hpb : IsPullback i' (pullback.fst f g) (ProjectiveSpace.map n g) i := by
    refine IsPullback.of_right (h₂₂ := ℙ(n; Spec (.of k)) ↘ Spec (.of k))
      (h₁₂ := ℙ(n; Spec (.of K)) ↘ Spec (.of K)) (v₁₃ := g) ?_
      (ProjectiveSpace.liftBaseChange_map _ _ _) (ProjectiveSpace.isPullback_map n g).flip
    rw [ProjectiveSpace.liftBaseChange_over, hif]
    exact (IsPullback.of_hasPullback f g).flip
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback hpb.flip hi
  refine ⟨n, i', hn, this, ProjectiveSpace.liftBaseChange_over _ _ _, ⟨?_⟩⟩
  exact (Scheme.Modules.pullback i').mapIso (ProjectiveSpace.pullbackMapTwistIso n g 1).symm ≪≫
    (Scheme.Modules.pullbackComp i' (ProjectiveSpace.map n g)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (ProjectiveSpace.liftBaseChange_map _ _ _)).app _ ≪≫
    (Scheme.Modules.pullbackComp (pullback.fst f g) i).symm.app _ ≪≫
    (Scheme.Modules.pullback (pullback.fst f g)).mapIso e

/-- **Ampleness is stable under field extension**, by
`AlgebraicGeometry.IsVeryAmple.pullback_of_field` applied to a very ample tensor power.

(blueprint: `lem-pc-very-ample-ample`) -/
theorem IsAmple.pullback_of_field {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}
    {M : X.Modules} (h : IsAmple f M) (K : Type u) [Field K] [Algebra k K] :
    IsAmple (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M) := by
  obtain ⟨hinv, m, hm, hv⟩ := h
  exact ⟨inferInstance, m, hm, (hv.pullback_of_field K).of_iso
    (Scheme.Modules.nonempty_pullback_tensorPow_iso _ M m).some⟩

/-- **Very ampleness descends along a field extension.** Let `X` be proper over a field `k`, let
`M` be an invertible `𝒪_X`-module and `K/k` a field extension such that `M_K` is very ample on
`X_K`. Then `M` is very ample. The closed immersion `X_K ⟶ ℙ(n; K)` is given by finitely many
sections of `M_K`, which lie in the `K`-span of finitely many sections of `M`, since
`H⁰(X_K, M_K) = H⁰(X, M) ⊗_k K`; these define a morphism `X ⟶ ℙ(V)` whose base change to `K`
is a closed immersion, hence which is a closed immersion by fpqc descent.

(blueprint: `lem-pc-very-ample-descends`) -/
theorem IsVeryAmple.of_pullback {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]
    (K : Type u) [Field K] [Algebra k K] (M : X.Modules) [M.IsInvertible]
    (h : IsVeryAmple (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M)) :
    IsVeryAmple f M :=
  sorry

open scoped Scheme.Modules in
/-- **The complement of an ample effective divisor is affine.** Let `X` be proper over a field
`k` and `D ⊆ X` an effective Cartier divisor, with invertible ideal sheaf `J = 𝒪_X(-D)`, whose
line bundle `𝒪_X(D) = J.toModulesᵛ` is ample. Then `X \ D` is affine, where the open
complement of `D` is presented by an open immersion `j` whose range is the complement of the
support of `J`. Choose `m` with `𝒪_X(mD)` very ample, embedding `X` by the complete linear
system into `ℙ^N`; the `m`-th power of the canonical section of `𝒪_X(D)` is the pullback of a
linear form `ℓ`, so `X \ D` is a closed subscheme of the affine space `ℙ^N \ V(ℓ)`.

(blueprint: `lem-sc-ample-complement-affine`) -/
theorem isAffine_compl_of_isAmple_dual_toModules {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hample : IsAmple f J.toModulesᵛ) {V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j.base = (J.support : Set X)ᶜ) :
    IsAffine V := by
  have := hJ.isInvertible_dual_toModules
  obtain ⟨-, m, hm, n, i, hn, hi, -, ⟨e⟩⟩ := hample
  obtain ⟨s, hs⟩ := hJ.exists_zeroLocus_eq
  let L := ProjectiveSpace.twistRestrict i 1
  have : L.IsInvertible := Scheme.Modules.IsInvertible.of_iso e.symm
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ X.Modules) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible _
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ (ℙ(n; Spec (.of k))).Modules) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible _
  -- The pullbacks `x l` of the coordinate sections, with non-vanishing loci `i⁻¹ D₊(T_l)`.
  let x (l : n) : 𝟙_ X.Modules ⟶ L := (Scheme.Modules.pullbackObjUnitIso i).inv ≫
    (Scheme.Modules.pullback i).map (ProjectiveSpace.coordinateSection n _ l)
  have hx (l : n) : (Scheme.Modules.Hom.zeroLocus (x l)).support.compl =
      i ⁻¹ᵁ ProjectiveSpace.standardOpen n _ l := by
    have h₁ : (x l).zeroLocus =
        ((Scheme.Modules.pullback i).map (ProjectiveSpace.coordinateSection n _ l)).zeroLocus :=
      Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _
        (Arrow.isoMk (Scheme.Modules.pullbackObjUnitIso _).symm (Iso.refl _)
          (Category.comp_id _).symm)
    rw [h₁, ← Scheme.Modules.Hom.comap_zeroLocus,
      ← ProjectiveSpace.compl_support_zeroLocus_coordinateSection]
    exact (congrArg TopologicalSpace.Closeds.compl
      (Scheme.IdealSheafData.support_comap _ i)).trans rfl
  -- The `m`-th power `t` of the canonical section of `𝒪_X(D)`, with non-vanishing locus `X \ D`.
  let t : 𝟙_ X.Modules ⟶ L := Scheme.Modules.tensorPowSection s m ≫ e.inv
  have ht : (Scheme.Modules.Hom.zeroLocus t).support.compl = J.support.compl := by
    have h₁ : (Scheme.Modules.tensorPowSection s m).zeroLocus = t.zeroLocus :=
      Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _
        (Arrow.isoMk (Iso.refl _) e.symm (by simp [t]))
    rw [← h₁, Scheme.Modules.compl_support_zeroLocus_tensorPowSection _ s hm, hs]
  have hU := Scheme.Modules.isAffineOpen_compl_support_zeroLocus f L x
    (fun l ↦ hx l ▸ (ProjectiveSpace.isAffineOpen_standardOpen n _ l).preimage i)
    (eq_top_iff.mpr fun p _ ↦ by
      obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((ProjectiveSpace.iSup_standardOpen n (Spec (.of k))).ge (Set.mem_univ (i p)))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, by rw [hx]; exact hl⟩) t
  have hr : j.opensRange = J.support.compl := by
    ext1
    exact hj
  rw [ht, ← hr] at hU
  have : IsAffine j.opensRange.toScheme := hU
  exact IsAffine.of_isIso j.isoOpensRange.hom

/-- **An ample module on a connected proper curve has positive degree.** Let `K` be
algebraically closed, `X` a connected proper curve over `K` and `L` an ample invertible
`𝒪_X`-module. Then `deg L = χ(L) - χ(𝒪_X) > 0`.

This is the connected case of blueprint `lem-sc-ample-positive-degree`, recorded there as
classical input without a separate proof. -/
@[stacks 0B5X]
theorem Scheme.Hom.degree_pos_of_isAmple_of_connectedSpace [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [IsProper f] [ConnectedSpace X] (hdim : topologicalKrullDim X = 1)
    (L : X.Modules) (hample : IsAmple f L) : 0 < f.degree L :=
  sorry

/-- Blueprint `sk-prop-av-ample-positive`: Ample modules on proper curves have positive degree.

Let `K` be algebraically closed, `C` a proper curve over `K` of dimension one (possibly
disconnected) and `L` an ample invertible `𝒪_C`-module. Then `deg L > 0`.

This is also blueprint `lem-sc-ample-positive-degree`. The proof decomposes `C` into its
finitely many connected components `C_i`, which are open and closed. The degree is additive
over them (`AlgebraicGeometry.Scheme.Modules.degree_eq_sum_of_pairwise_disjoint`); a component
of dimension `0` is a single point, so contributes `0`; a component of dimension `1` contributes
a positive degree by the connected case
`AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple_of_connectedSpace`, since `L|_{C_i}` is
ample (`AlgebraicGeometry.IsAmple.pullback`). If all components had dimension `0`,
`C` would be discrete, so at least one has dimension `1`. -/
theorem Scheme.Hom.degree_pos_of_isAmple [IsAlgClosed K] (f : X ⟶ Spec (.of K)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) (L : X.Modules) (hample : IsAmple f L) :
    0 < f.degree L := by
  have := hample.isInvertible
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of K)) := ‹IsProper f›
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have : Fintype (ConnectedComponents X) := Fintype.ofFinite _
  -- The connected components `U c` of `X`, open and closed in `X`.
  let U (c : ConnectedComponents X) : X.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {c}, (isOpen_discrete {c}).preimage
      ConnectedComponents.continuous_coe⟩
  have hU : _root_.Pairwise (Disjoint on U) := fun c d hcd ↦
    Opens.coe_disjoint.mp ((Set.disjoint_singleton.mpr hcd).preimage ConnectedComponents.mk)
  have hcover : ⨆ c, U c = ⊤ := eq_top_iff.mpr fun x _ ↦
    Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, rfl⟩
  let (c : ConnectedComponents X) : (U c).toScheme.Over (Spec (.of K)) := ⟨(U c).ι ≫ f⟩
  have hdimU (c : ConnectedComponents X) :
      topologicalKrullDim (U c) = 1 ∨ topologicalKrullDim (U c) ≤ 0 := by
    rcases (hdim ▸ topologicalKrullDim_subspace_le X (U c)).lt_or_eq with h | h
    · exact Or.inr (Order.le_of_lt_succ h)
    · exact Or.inl h
  -- Each component contributes a nonnegative degree, positive if it has dimension `1`.
  have hdeg (c : ConnectedComponents X) :
      0 ≤ ((Scheme.Modules.pullback (U c).ι).obj L).degree K ∧
      (topologicalKrullDim (U c) = 1 →
        0 < ((Scheme.Modules.pullback (U c).ι).obj L).degree K) := by
    have : ConnectedSpace (U c) := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      have : (U x : Set X) = connectedComponent x := connectedComponents_preimage_singleton
      exact isConnected_iff_connectedSpace.mp (this ▸ isConnected_connectedComponent)
    have hclosed : IsClosed (U c : Set X) :=
      (isClosed_discrete {c}).preimage ConnectedComponents.continuous_coe
    have : IsClosedImmersion (U c).ι := .of_isPreimmersion _ (by simpa using hclosed)
    have hpos (h1 : topologicalKrullDim (U c) = 1) :
        0 < ((Scheme.Modules.pullback (U c).ι).obj L).degree K := by
      have := ((U c).ι ≫ f).degree_pos_of_isAmple_of_connectedSpace h1 _ (hample.pullback _)
      rwa [degree_eq_degree_of_topologicalKrullDim_eq_one _ h1] at this
    refine ⟨?_, hpos⟩
    rcases hdimU c with h | h
    · exact (hpos h).le
    · exact (Scheme.Modules.degree_eq_zero_of_topologicalKrullDim_le_zero K h _).ge
  rw [degree_eq_degree_of_topologicalKrullDim_eq_one f hdim,
    Scheme.Modules.degree_eq_sum_of_pairwise_disjoint K hdim.le U hU hcover L]
  refine Finset.sum_pos' (fun c _ ↦ (hdeg c).1) ?_
  -- Some component has dimension `1`: otherwise every component is discrete, hence so is `X`.
  by_contra! h
  have : DiscreteTopology X := by
    refine discreteTopology_iff_isOpen_singleton.mpr fun x ↦ ?_
    have := IsLocallyArtinian.of_topologicalKrullDim_le_zero
      ((hdimU (ConnectedComponents.mk x)).resolve_left fun h1 ↦
        (h _ (Finset.mem_univ _)).not_gt ((hdeg _).2 h1))
    have hd : DiscreteTopology (U (ConnectedComponents.mk x)) :=
      IsLocallyArtinian.discreteTopology (X := (U (ConnectedComponents.mk x)).toScheme)
    have := (U (ConnectedComponents.mk x)).isOpen.isOpenMap_subtype_val _
      (@isOpen_discrete _ _ hd {(⟨x, rfl⟩ : U (ConnectedComponents.mk x))})
    convert this using 1
    ext y
    constructor
    · rintro rfl
      exact ⟨⟨y, rfl⟩, rfl, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_singleton_iff.mp hz]
      rfl
  have := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at this
  exact absurd this (by decide)

/-- **An ample module has positive degree.** Let `X` be a nonempty proper scheme over a field
`K` and `M` an ample invertible `𝒪_X`-module. Then the degree of `X` with respect to `M` is
positive.

This is Stacks 0BEV, cited as classical input in the proof of blueprint `sk-prop-av-isogeny`
(also `lem-sc-isogeny-facts`). -/
@[stacks 0BEV]
theorem Scheme.Hom.degree_pos_of_isAmple_of_nonempty (f : X ⟶ Spec (.of K)) [IsProper f]
    [Nonempty X] (M : X.Modules) (hample : IsAmple f M) : 0 < f.degree M :=
  sorry

/-- **An ample module on a proper curve is not trivial.** Let `K` be algebraically closed, `X` a
proper curve over `K` and `L` an ample invertible `𝒪_X`-module. Then `L ≇ 𝒪_X`: `L` has positive
degree (`AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple`), whereas `𝒪_X` has degree `0`.

This is the last assertion of blueprint `lem-sc-ample-positive-degree`. -/
theorem IsAmple.isEmpty_iso_unit [IsAlgClosed K] {f : X ⟶ Spec (.of K)} [IsProper f]
    (hdim : topologicalKrullDim X = 1) {L : X.Modules} (hL : IsAmple f L) :
    IsEmpty (L ≅ 𝟙_ X.Modules) := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  refine ⟨fun e ↦ ?_⟩
  have := f.degree_pos_of_isAmple hdim L hL
  rw [Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one f hdim,
    Scheme.Modules.degree_congr K e] at this
  exact this.ne' (Scheme.Modules.degree_unit K)

/-- **No positive tensor power of an ample module on a proper curve is trivial.** Let `K` be
algebraically closed, `X` a proper curve over `K` and `L` an ample invertible `𝒪_X`-module. For
`0 < k` the module `L^{⊗ k}` is again ample (`AlgebraicGeometry.IsAmple.tensorPow`), so it has
positive degree (`AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple`), whereas `𝒪_X` has degree
`0`.

This is used in the proof of blueprint `lem-sc-mult-n-finite-kernel`. -/
theorem IsAmple.isEmpty_tensorPow_iso_unit [IsAlgClosed K] {f : X ⟶ Spec (.of K)} [IsProper f]
    (hdim : topologicalKrullDim X = 1) {L : X.Modules} (hL : IsAmple f L)
    {k : ℕ} (hk : 0 < k) : IsEmpty (L.tensorPow k ≅ 𝟙_ X.Modules) := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  refine ⟨fun e ↦ ?_⟩
  have := f.degree_pos_of_isAmple hdim _ (hL.tensorPow hk)
  rw [Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one f hdim,
    Scheme.Modules.degree_congr K e] at this
  exact this.ne' (Scheme.Modules.degree_unit K)

open scoped fwdDiff in
/-- **The leading coefficient of a twisted Hilbert function only depends on the generic rank.**
Let `Y` be an integral proper `K`-scheme of dimension `g`, `M` an ample invertible `𝒪_Y`-module
and `E` a coherent `𝒪_Y`-module which is free of rank `r` on a nonempty open subset of `Y`. Then
the `g`-th forward difference at `0` of `m ↦ χ(Y, E ⊗ M^{⊗ m})` is `r` times the degree of `Y`
with respect to `M`. Both `m ↦ χ(Y, E ⊗ M^{⊗ m})` and `m ↦ r χ(Y, M^{⊗ m})` are numerical
polynomials of degree at most `g` (blueprint `lem-sc-hilbert-polynomial`), and their difference
has degree at most `g - 1`: by additivity of `χ` and dévissage, `E` may be compared with
`𝒪_Y^{⊕ r}` up to coherent modules supported on a proper closed subset, of dimension `< g`.

This is the input on Hilbert polynomials used in the proof of blueprint
`lem-sc-deg-pullback-finite`. -/
theorem Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [IsProper f] (M : Y.Modules) (hample : IsAmple f M)
    (E : Y.Modules) [E.IsFinitePresentation] {U : Y.Opens} (hU : (U : Set Y).Nonempty) {r : ℕ}
    (e : (Scheme.Modules.pullback U.ι).obj E ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    letI : Y.Over (Spec (.of K)) := ⟨f⟩
    Δ_[1]^[((topologicalKrullDim Y).unbotD 0).toNat]
      (fun m ↦ Scheme.Modules.eulerChar K (E ⊗ M.tensorPow m)) 0 = r * f.degree M :=
  sorry

/-- Blueprint `sk-prop-av-deg-pullback`: Degree of a pullback under a finite morphism.

Let `g : X ⟶ Y` be a finite surjective morphism of proper `K`-varieties of the same dimension,
let `M` be an ample invertible `𝒪_Y`-module and let `d = [k(X) : k(Y)]` be the degree of `g`.
Then `deg_{g^*M}(X) = d * deg_M(Y)`.

This is also blueprint `lem-sc-deg-pullback-finite` (Stacks 0BEX). Both sides are `g`-th forward
differences at `0`, where `dim X = dim Y` since `g` is finite surjective
(`AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_of_surjective`). By the projection formula
`χ(X, (g^* M)^{⊗ m}) = χ(X, g^* M^{⊗ m}) = χ(Y, g_* g^* M^{⊗ m}) = χ(Y, g_* 𝒪_X ⊗ M^{⊗ m})`, and
`g_* 𝒪_X` is a coherent module of generic rank `d`, so the leading coefficients compare by
`AlgebraicGeometry.Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow`.

```
  X ────────── g ─────────▶ Y
    ╲                       │
     ╲  fX                  │ fY
      ╲                     ▼
       ╲───────────▶ Spec K
```
-/
theorem Scheme.Hom.degree_pullback [IsIntegral X] [IsIntegral Y] (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) [IsProper fX] [IsProper fY] (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [IsFinite g] [Surjective g] (M : Y.Modules) (hample : IsAmple fY M) :
    fX.degree ((Scheme.Modules.pullback g).obj M) =
      g.finrank (genericPoint Y) * fY.degree M := by
  have := hample.isInvertible
  subst hg
  let : Y.Over (Spec (.of K)) := ⟨fY⟩
  let : X.Over (Spec (.of K)) := ⟨g ≫ fY⟩
  have : g.IsOver (Spec (.of K)) := ⟨rfl⟩
  have := LocallyOfFiniteType.isLocallyNoetherian fY
  have := Scheme.Modules.isFinitePresentation_pushforward_unit g
  obtain ⟨U, hU, ⟨e⟩⟩ := Scheme.Modules.exists_pullback_pushforward_unit_iso_free g
  rw [← fY.fwdDiff_iter_eulerChar_tensorObj_tensorPow M hample _ hU e, degree,
    g.topologicalKrullDim_eq_of_surjective]
  refine congrArg (fun F : ℕ → ℤ ↦ (fwdDiff 1)^[_] F 0) (funext fun m ↦ ?_)
  -- `χ(X, (g^* M)^{⊗ m}) = χ(X, g^* M^{⊗ m}) = χ(Y, g_* g^* M^{⊗ m}) = χ(Y, g_* 𝒪_X ⊗ M^{⊗ m})`
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso g M m
  obtain ⟨e₂⟩ := Scheme.Modules.nonempty_pushforward_pullback_iso g (M.tensorPow m)
  change Scheme.Modules.eulerChar K _ = _
  rw [← Scheme.Modules.eulerChar_congr K e₁, ← Scheme.Modules.eulerChar_congr K e₂,
    Scheme.Modules.eulerChar_pushforward_of_isAffineHom]

end AlgebraicGeometry
