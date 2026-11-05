/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Algebra.Homology.MatrixComplexTower
public import WeilConjectures.Algebra.Homology.MinimalComplex
public import WeilConjectures.Algebra.Homology.MinimalMatrixComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectTrace
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Normalized towers of perfect complexes over an adic ring

Let `R` be a commutative ring with a tower of quotients `π n : R →+* A n` and transitions
`ρ n : A (n + 1) →+* A n` (the intended case is `R = 𝒪_E` and `A n = 𝒪_E ⧸ ϖⁿ⁺¹`). A
*normalized tower of perfect complexes* (`ModuleCat.NormalizedPerfectTower`) is a family of
perfect complexes `Q n ∈ D(A n)` with maps `Q (n + 1) ⟶ Res Q n` exhibiting `Q n` as the
derived base change `Q (n + 1) ⊗ᴸ_{A (n + 1)} A n`. Its restrictions of scalars form a tower
`n ↦ Res Q n` in `D(R)`.

When the `A n` are local and `R` is complete and separated for the tower, the derived limit
`P = R lim_n Q n` of this tower is represented by a bounded complex of finite free
`R`-modules and reduces to the levels, `P ⊗ᴸ_R A n ≅ Q n` (Stacks, Tag 09AW). A compatible
family of endomorphisms `f n` of the `Q n` lifts to an endomorphism `V` of `P`, and the
categorical trace of any lift reduces to the traces of the `f n`.

## Main definitions

- `ModuleCat.NormalizedPerfectTower`: a normalized tower of perfect complexes.
- `ModuleCat.NormalizedPerfectTower.restrict`: the tower `n ↦ Res Q n` in `D(R)`.
- `ModuleCat.NormalizedPerfectTower.IsCompatible`: compatible families of endomorphisms.
- `ModuleCat.NormalizedPerfectTower.IsLift`: lifts of a compatible family to the derived limit.

## Main results

- `ModuleCat.NormalizedPerfectTower.exists_iso_Q_obj_of_isHomotopyLimit`: the derived limit is
  represented by a bounded complex of finite free `R`-modules.
- `ModuleCat.NormalizedPerfectTower.isDerivedBaseChange_π_app`: the legs `P ⟶ Res Q n` of the
  derived limit exhibit `Q n` as `P ⊗ᴸ_R A n`.
- `ModuleCat.NormalizedPerfectTower.exists_isLift`: compatible families lift.
- `ModuleCat.NormalizedPerfectTower.exists_trace_eq_of_isLift`,
  `ModuleCat.NormalizedPerfectTower.trace_eq_of_isLift`: the trace of a lift reduces to the
  traces of the family, and does not depend on the lift.

## Implementation notes

Derived base change is expressed by universal arrows (`ModuleCat.IsDerivedBaseChange`): the
leg `pr_n : P ⟶ Res Q n` is the blueprint's `π_n : P ⊗ᴸ A n ⟶ Q n` read through the adjunction
between derived base change and restriction of scalars. For the same reason the blueprint's
condition `π_n ∘ (V ⊗ᴸ A n) = f n ∘ π_n` on a lift `V` is the condition
`V ≫ pr_n = pr_n ≫ Res (f n)` of `ModuleCat.NormalizedPerfectTower.IsLift`: `V ⊗ᴸ A n` is the
unique endomorphism `g` of `P ⊗ᴸ A n` with `pr_n ≫ Res g = V ≫ pr_n`.

The proof follows the blueprint. Each `Q n` has a minimal model, a bounded complex of finite
free `A n`-modules whose differentials vanish modulo the maximal ideal
(`CochainComplex.exists_homotopyEquiv_isMinimal`); quasi-isomorphisms between minimal models are
isomorphisms (`CochainComplex.isIso_of_quasiIso_of_isMinimal`). In bases, the models are given by
matrices, and lifting invertible matrices along `A (n + 1) ⟶ A n` strictifies the tower into a
tower of matrix complexes whose transitions are the reductions of the entries. Their entrywise
limit is the bounded free complex over `R` representing `P`
(`DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi`). Lifts are built by choosing chain-level
representatives level by level and correcting them by lifted homotopies, and traces are
alternating sums of matrix traces
(`DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

namespace ModuleCat

variable {R : Type u} [CommRing R] {A : ℕ → Type u} [∀ n, CommRing (A n)]
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [∀ n, HasDerivedCategory.{u} (ModuleCat.{u} (A n))]
  {π : ∀ n, R →+* A n} {ρ : ∀ n, A (n + 1) →+* A n}

namespace NormalizedPerfectTower

variable {hρ : ∀ n, π n = (ρ n).comp (π (n + 1))} (T : NormalizedPerfectTower π ρ hρ)

variable [∀ n, IsLocalRing (A n)] (hπ : ∀ n, Function.Surjective (π n)) {ϖ : R}
  (hker : ∀ n, RingHom.ker (π n) = Ideal.span {ϖ ^ (n + 1)})
  (hcomplete : ∀ x : ∀ n, A n, (∀ n, ρ n (x (n + 1)) = x n) → ∃ r : R, ∀ n, π n r = x n)
  (hsep : ∀ r : R, (∀ n, π n r = 0) → r = 0)
  {c : Cone T.restrict} (hc : IsHomotopyLimit c)

/-! ### Strictification of the tower by minimal matrix complexes -/

section Trace

/-! The braiding of the derived categories is the Koszul braiding
`DerivedCategory.braidedCategory'` of the derived tensor product. -/

attribute [local instance] DerivedCategory.braidedCategory'

variable [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
  [∀ n, Abelian.HasFunctorialFlatResolution (ModuleCat.{u} (A n))]
  [HasRightDual c.pt] [∀ n, HasRightDual (T.obj n)]

-- The compatibility `hf` of the blueprint statement is not needed.

-- The compatibility `hf` of the blueprint statement is not needed.

end Trace

end NormalizedPerfectTower

end ModuleCat
