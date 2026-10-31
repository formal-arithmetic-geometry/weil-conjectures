/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import WeilConjectures.Algebra.Category.ModuleCat.StableImageTower

/-!
# Stable images and adic cofinality for finite module towers

Source: latest Weil blueprint, `prop-zl-smooth-proper-relative-purity`, proof, Step 1,
Passage to the limit; Stacks Project Tags 0596 and 0597
(blueprint: lem-zl-finite-tower-stable-images).

Index `n : ℕ` denotes the positive level `n + 1`. A module over `A / π^(n+1)` is
encoded as an `A`-module annihilated by `π^(n+1)`. The functor encodes all transition
composites. The topology binder is fixed to the initial topology of the discrete projections.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace Padic

/-- Stable images of an arbitrary finite coefficient-module tower are the projection images;
the projection kernels are cofinal with the adic powers of its finitely generated limit.

Source: latest blueprint, `prop-zl-smooth-proper-relative-purity`, proof, Step 1,
Passage to the limit; Stacks Tags 0596 and 0597
(blueprint: lem-zl-finite-tower-stable-images).

Proof (the node's steps; Lean level `n` is the node's level `n + 1`):
1. Fix `n`. The images `I_m` of `t_{m,n}` decrease in `m`, since
   `t_{k,n} = t_{m,n} t_{k,m}`. As `N_n` is finite, choose `m₀ ≥ n` with `|I_{m₀}|`
   minimal; then `I_m = I_{m₀}` for `m ≥ m₀`, and `B_n = I_{m₀}`
   (def-weil-inverse-system; Stacks 0595, 0596).
2. Transitions map `B_{n+1}` into `B_n`. For surjectivity take `k ≥ n + 1` beyond the
   stabilization indices of `n` and `n + 1`, write `b = t_{k,n}(z)`; then
   `t_{k,n+1}(z) ∈ B_{n+1}` maps to `b`.
3. `p_n(x) ∈ B_n` by compatibility. Conversely, for `b ∈ B_n` the fibres
   `E_m = {z ∈ B_m : t_{m,n}(z) = b}`, `m ≥ n`, are nonempty with surjective adjacent maps by
   Step 2; lem-weil-pbc-ml-sets-tower-limit-nonempty gives a compatible family, extended
   below `n` by `t_{n,j}(b)`. Hence `im p_n = B_n` (Stacks 0597).
4. `x + U_n ↦ p_n(x)` is well defined and injective as `U_n = ker p_n`, and surjective by
   Step 3: the isomorphism `N / U_n ≅ B_n` normalized by `p_n`.
5. Each `U_n = p_n⁻¹{0}` is open; the `U_n` decrease since `p_n = t_n p_{n+1}`; a basic
   neighbourhood of zero constrains finitely many coordinates, so contains some `U_n`;
   `⋂ U_n = 0`; `N` is Hausdorff; `π^(n+1) N ⊆ U_n` because `N_n` is killed by `π^(n+1)`.
6. Choose generators of `N` (def-weil-finitely-generated-module) and the surjection
   `f : A^d → N`. Each `p_n f` factors through `(A/π^(n+1))^d`, continuous by
   lem-sfb-integers-profinite-tower (1), so `f` is continuous; `A` is compact by
   lem-sfb-integers-profinite-tower (2) and `A^d` by
   lem-weil-pbc-tychonoff-product-quasi-compact. By
   lem-sfb-compact-hausdorff-surjection-quotient and Step 5, `f` is a quotient map
   (`d = 0` included).
7. For `r ≥ 1`, `π^r A` is open (lem-sfb-integers-profinite-tower (1)), and
   `f⁻¹(π^r N) = π^r A^d + ker f` is a union of its cosets, so `π^r N` is open by Step 6;
   by Step 5 some `U_n ⊆ π^r N`. With `π^(n+1) N ⊆ U_n` the two families are cofinal, so the
   inverse-limit topology is the `π`-adic topology.
No surjectivity of the original transitions is used. -/
theorem finiteTower_stable_images
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (π : coefficientExtensionIntegers l E)
    (hπ : Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) =
      coefficientExtensionMaximalIdeal l E)
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} (coefficientExtensionIntegers l E))
    [∀ n : ℕ, Finite (F.obj (op n))]
    (hkill : ∀ (n : ℕ) (x : F.obj (op n)), π ^ (n + 1) • x = 0)
    [Module.Finite (coefficientExtensionIntegers l E)
      (ModuleCat.carrier (limit F))]
    (τ : TopologicalSpace (ModuleCat.carrier (limit F)))
    (hτ : τ = ⨅ n : ℕ, TopologicalSpace.induced (limit.π F (op n)) ⊥) :
    (∀ n : ℕ, ∃ (m₀ : ℕ) (hn : n ≤ m₀), ∀ (m : ℕ) (hm : m₀ ≤ m),
      ModuleCat.towerRange F (hn.trans hm) = ModuleCat.stableImage F n) ∧
    (∀ n : ℕ, LinearMap.range (limit.π F (op n)).hom = ModuleCat.stableImage F n) ∧
    (∀ n : ℕ, Function.Surjective
      ((ModuleCat.stableImageTower F).map (homOfLE (Nat.le_succ n)).op)) ∧
    (∀ n : ℕ, ∃ e : ((ModuleCat.carrier (limit F)) ⧸ LinearMap.ker (limit.π F (op n)).hom) ≃ₗ[
        coefficientExtensionIntegers l E] ModuleCat.stableImage F n,
      ∀ x : (ModuleCat.carrier (limit F)), (e (Submodule.Quotient.mk x) : F.obj (op n)) =
        (limit.π F (op n)) x) ∧
    τ = (Ideal.span ({π} : Set (coefficientExtensionIntegers l E))).adicModuleTopology
      (ModuleCat.carrier (limit F)) ∧
    Antitone (fun n : ℕ ↦ LinearMap.ker (limit.π F (op n)).hom) ∧
    (∀ n : ℕ, @IsOpen (ModuleCat.carrier (limit F)) τ
      (LinearMap.ker (limit.π F (op n)).hom : Set (ModuleCat.carrier (limit F)))) ∧
    (@nhds (ModuleCat.carrier (limit F)) τ 0).HasBasis (fun _n : ℕ ↦ True)
      (fun n : ℕ ↦ (LinearMap.ker (limit.π F (op n)).hom : Set (ModuleCat.carrier (limit F)))) ∧
    (⨅ n : ℕ, LinearMap.ker (limit.π F (op n)).hom) = ⊥ ∧
    (∀ n : ℕ, (Ideal.span ({π} : Set (coefficientExtensionIntegers l E))) ^ (n + 1) •
      (⊤ : Submodule (coefficientExtensionIntegers l E) (ModuleCat.carrier (limit F))) ≤
        LinearMap.ker (limit.π F (op n)).hom) ∧
    (∀ r : ℕ, 1 ≤ r → ∃ n : ℕ, LinearMap.ker (limit.π F (op n)).hom ≤
      (Ideal.span ({π} : Set (coefficientExtensionIntegers l E))) ^ r •
        (⊤ : Submodule (coefficientExtensionIntegers l E) (ModuleCat.carrier (limit F)))) := by
  sorry

end Padic
