/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.Algebra.Module.GradedLocalizationExact

/-!
# Eventual isomorphism from degree-zero localizations

Source: Stacks Project, coherent.tex, Tag 0AG7, lemma-recover-tail-graded-module,
second half of the proof (blueprint: lem-sfb-graded-local-isomorphism-tail).

The three auxiliary definitions only package the generator conditions, the displayed
numerical bound, and the kernel/cokernel conclusions of this statement. Truncations,
kernel and quotient are specified by their canonical subgroups and quotient maps.
-/

@[expose] public section

universe u v w

namespace LocalizedModule

/-- The homogeneous generating and annihilating conditions in Stacks Tag 0AG7,
lemma-recover-tail-graded-module, final paragraph. Empty families are permitted.
(blueprint: lem-sfb-graded-local-isomorphism-tail) -/
def IsTailGeneratingFamily {S : Type u} [CommRing S] {T : Type v}
    [AddCommGroup T] [Module S T] {r k : ℕ} (f : Fin r → S)
    (𝓣 : ℤ → AddSubgroup T) (t : Fin k → T) (e : Fin k → ℕ)
    (b : Fin r → Fin k → ℕ) : Prop :=
  Submodule.span S (Set.range t) = ⊤ ∧
  (∀ j, t j ∈ 𝓣 (e j)) ∧
  (∀ i j, 1 ≤ b i j) ∧ ∀ i j, f i ^ b i j • t j = 0

/-- The maximum of zero and the numbers `e j + ∑ i, b i j`, including the empty-family
case, in Stacks Tag 0AG7, lemma-recover-tail-graded-module, final paragraph.
(blueprint: lem-sfb-graded-local-isomorphism-tail) -/
def tailGeneratorBound {r k : ℕ} (e : Fin k → ℕ) (b : Fin r → Fin k → ℕ) : ℕ :=
  Finset.univ.sup (fun j ↦ e j + ∑ i, b i j)

/-- All conclusions for one of the nonnegative kernel and cokernel in Stacks Tag 0AG7:
finite compatible grading, zero negative and localized pieces, a homogeneous annihilating
family giving `B`, and the vanishing bound for every such family.
(blueprint: lem-sfb-graded-local-isomorphism-tail) -/
def GradedTailConclusion {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S)
    {r : ℕ} (f : Fin r → S) {T : Type v} [AddCommGroup T] [Module S T]
    (𝓣 : ℤ → AddSubgroup T) (B : ℕ) : Prop :=
  Module.Finite S T ∧ DirectSum.IsInternal 𝓣 ∧
  (∀ (a : ℕ) (n : ℤ) (s : S) (x : T),
    s ∈ 𝒜 a → x ∈ 𝓣 n → s • x ∈ 𝓣 ((a : ℤ) + n)) ∧
  (∀ n : ℤ, n < 0 → 𝓣 n = ⊥) ∧
  (∀ i, ∀ x ∈ degreeZeroFractions (fun a : ℕ ↦ (𝒜 a : Set S))
    (fun a : ℕ ↦ (𝓣 a : Set T)) (Submonoid.powers (f i)), x = 0) ∧
  (∃ (k : ℕ) (t : Fin k → T) (e : Fin k → ℕ) (b : Fin r → Fin k → ℕ),
    IsTailGeneratingFamily f 𝓣 t e b ∧ B = tailGeneratorBound e b) ∧
  (∀ (k : ℕ) (t : Fin k → T) (e : Fin k → ℕ) (b : Fin r → Fin k → ℕ),
    IsTailGeneratingFamily f 𝓣 t e b →
    ∀ n : ℤ, (tailGeneratorBound e b : ℤ) < n → ∀ x ∈ 𝓣 n, x = 0)

/-- A degree-preserving map that is an isomorphism on the standard degree-zero
localizations is an isomorphism in all sufficiently high degrees, with the explicit
kernel/cokernel and generator bounds of Stacks Tag 0AG7.

The existential submodules are uniquely specified nonnegative truncations; the formula
for `φ` uniquely specifies the restriction of `ψ`. The kernel pieces are inverse images
under the inclusion into `M`; the cokernel pieces are images under the quotient map.
The additive equivalence in the last clause is the degreewise map `ψ`, and its scalar
formula expresses linearity over `𝒜 0` without selecting new module instances.

Source: Stacks Project, coherent.tex, Tag 0AG7, lemma-recover-tail-graded-module,
second half of the proof (blueprint: lem-sfb-graded-local-isomorphism-tail).

Proof:
1. Nonnegative pieces form submodules, since scalar degrees are nonnegative. Restrict
   ψ. Its kernel and image are homogeneous, by uniqueness of homogeneous components;
   the quotient has pieces N_n/ψ(M_n) in nonnegative degrees and zero negative pieces.
2. By lem-weil-pbc-noetherian-submodule-finite, M+ and the kernel are finite.
   The quotient is finite as a quotient of N+ (def-weil-finitely-generated-module).
3. Nonnegative truncation preserves degree-zero fractions: numerators have degree a
   with a >= 0. The fraction relation is unchanged, as are addition and scalar action,
   so the restricted localized map is an isomorphism.
4. Extend the ring grading by zero to negative degrees. Apply
   lem-sc-graded-localization-exact to the kernel-map-cokernel exact sequence.
   Since its middle localized map is bijective, both end localizations vanish.
5. Decompose finite generators into their finitely many homogeneous components.
   These generate and have nonnegative degree. Use the empty family for zero modules.
6. Each t_j/f_i^e_j is zero. The ordinary localization relation gives f_i^k t_j = 0;
   replace k by max(1,k), allowing also zero and nilpotent f_i.
7. For any permitted family, expand coefficients into polynomials in the f_i over S_0
   and project to degree n. Only terms c * product(f_i^a_i) * t_j with total degree
   e_j + sum(a_i) = n survive.
8. If n exceeds the displayed bound, some a_i >= b_ij, so every term vanishes.
   If r = 0 there are only degree-zero monomials; empty t gives the zero module.
9. Above 1 + max(B_K,B_Q), both degreewise kernel and cokernel vanish, so ψ_n is
   bijective. Its inverse is additive and S_0-linear by applying the injective ψ_n
   to the addition and scalar identities. No negative-degree finiteness of N is used.
-/
theorem graded_local_isomorphism_tail
    {S : Type u} [CommRing S] [IsNoetherianRing S]
    (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (r : ℕ) (f : Fin r → S) (hf : ∀ i, f i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤)
    {M : Type v} [AddCommGroup M] [Module S M] [Module.Finite S M]
    {N : Type w} [AddCommGroup N] [Module S N]
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (𝓝 : ℤ → AddSubgroup N) (h𝓝 : DirectSum.IsInternal 𝓝)
    (hsmulM : ∀ (a : ℕ) (n : ℤ) (s : S) (x : M),
      s ∈ 𝒜 a → x ∈ 𝓜 n → s • x ∈ 𝓜 ((a : ℤ) + n))
    (hsmulN : ∀ (a : ℕ) (n : ℤ) (s : S) (x : N),
      s ∈ 𝒜 a → x ∈ 𝓝 n → s • x ∈ 𝓝 ((a : ℤ) + n))
    (ψ : M →ₗ[S] N) (hψ : ∀ n x, x ∈ 𝓜 n → ψ x ∈ 𝓝 n)
    (hfinite : (Submodule.span S (⋃ n : ℕ, (𝓝 n : Set N))).FG)
    (hloc : ∀ i, Set.BijOn
      (IsLocalizedModule.map (Submonoid.powers (f i))
        (mkLinearMap (Submonoid.powers (f i)) M)
        (mkLinearMap (Submonoid.powers (f i)) N) ψ)
      (degreeZeroFractions (fun a : ℕ ↦ (𝒜 a : Set S))
        (fun a : ℕ ↦ (𝓜 a : Set M)) (Submonoid.powers (f i)))
      (degreeZeroFractions (fun a : ℕ ↦ (𝒜 a : Set S))
        (fun a : ℕ ↦ (𝓝 a : Set N)) (Submonoid.powers (f i)))) :
    ∃ (P : Submodule S M) (R : Submodule S N) (φ : P →ₗ[S] R),
      P.toAddSubgroup = (⨆ n : ℕ, 𝓜 n) ∧
      R.toAddSubgroup = (⨆ n : ℕ, 𝓝 n) ∧
      (∀ x : P, (φ x : N) = ψ (x : M)) ∧
      ∃ (𝓚 : ℤ → AddSubgroup φ.ker) (𝓠 : ℤ → AddSubgroup (R ⧸ φ.range))
        (BK BQ : ℕ),
        (∀ n, 𝓚 n = (𝓜 n).comap
          (P.subtype.comp φ.ker.subtype).toAddMonoidHom) ∧
        (∀ n, 𝓠 n = ((𝓝 n).comap R.subtype.toAddMonoidHom).map
          φ.range.mkQ.toAddMonoidHom) ∧
        GradedTailConclusion 𝒜 f 𝓚 BK ∧ GradedTailConclusion 𝒜 f 𝓠 BQ ∧
        ∀ n : ℤ, ((1 + max BK BQ : ℕ) : ℤ) ≤ n →
          ∃ e : 𝓜 n ≃+ 𝓝 n,
            (∀ x : 𝓜 n, (e x : N) = ψ (x : M)) ∧
            ∀ (a : 𝒜 0) (x y : 𝓜 n), (y : M) = (a : S) • (x : M) →
              (e y : N) = (a : S) • (e x : N) := by
  sorry

end LocalizedModule
