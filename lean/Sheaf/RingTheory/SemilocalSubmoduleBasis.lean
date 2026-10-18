/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.LocalRing.Module

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.OrzechProperty
import Mathlib.RingTheory.LocalProperties.Exactness
import WeilConjectures.Mathlib.GroupTheory.CosetCover

/-!
# A generating submodule contains a basis over a semilocal algebra

Source: Stacks Project, Algebra, Tags 03C1 and 02M9
(blueprint: lem-a1-semilocal-submodule-basis).
-/

@[expose] public section

universe u v w

namespace Module

/-- A generating `D`-submodule contains an `E`-basis of a constant-rank finite locally
free module over a semilocal `D`-algebra. The local ring `D` has infinite residue field,
and its maximal ideal extends into the Jacobson radical of `E`.

Source: Stacks Project, Algebra, Tags 03C1 and 02M9.
(blueprint: lem-a1-semilocal-submodule-basis)

Proof:
1. Enumerate the maximal ideals `qᵢ` of `E`. The radical hypothesis gives embeddings
   `k = D/m → E/qᵢ = kᵢ`, so the images of `N` in `Fᵢ = P/qᵢP` are `k`-linear.
2. Choose a principal trivializing open containing each `qᵢ`. Localize its rank-`r`
   basis further to get `P_qᵢ ≃ E_qᵢ^r`. On fractions the comparison sends
   `(p/f^a)/s` to `p/(f^a s)`, with inverse `p/s ↦ (p/1)/s`.
3. Reduction identifies `P_qᵢ/qᵢP_qᵢ` with `Fᵢ` by `[p/s] ↦ s̄⁻¹[p]`, with inverse
   `[p] ↦ [p/1]`. Thus `Fᵢ` has dimension `r` over `kᵢ`.
4. Lift coordinate bases of the finitely many `Fᵢ` and express the lifts using `N`.
   Collect the finitely many elements of `N` used into `x₁,...,x_L`. The maps
   `Tᵢ : k^L → Fᵢ`, `c ↦ ∑ cⱼ[xⱼ]`, have `kᵢ`-spanning images.
5. Inductively choose `n₁,...,n_r` in `N` with independent images in every `Fᵢ`.
   Before step `t+1`, the inverse images under `Tᵢ` of the spans of the first `t`
   images are proper `k`-subspaces. Avoid their finite union by
   `lem-pc-finite-linear-avoidance`, lift the chosen coefficients to `D`, and take
   the corresponding combination of the `xⱼ`. At `t=r` every residue family is a basis.
6. The map `φ : E^r → P` defined by these vectors is surjective at each maximal
   localization by `lem-weil-pbc-nakayama-local-generators`.
7. Compose `φ_qᵢ` with the rank-`r` trivialization. The resulting surjective finite
   endomorphism is bijective by `lem-weil-pbc-finite-module-surjective-endomorphism-bijective`.
8. Apply `lem-weil-pbc-linear-map-bijective-at-maximal-localizations` to `φ`.
   Its inverse gives the desired basis, all of whose vectors were chosen in `N`.
   If `E` is the zero ring, the maximal spectrum and the avoidance family are empty;
   `P=0` and the same conclusion holds. -/
theorem exists_basis_mem_submodule_of_semilocal
    {D : Type u} [CommRing D] [IsLocalRing D]
    [Infinite (IsLocalRing.ResidueField D)]
    {E : Type v} [CommRing E] [Algebra D E] [Finite (MaximalSpectrum E)]
    (hjac : Ideal.map (algebraMap D E) (IsLocalRing.maximalIdeal D) ≤
      Ideal.jacobson (⊥ : Ideal E))
    {P : Type w} [AddCommGroup P] [Module E P] [Module D P] [IsScalarTower D E P]
    (r : ℕ) (hr : 1 ≤ r)
    (hfree : ∃ s : Finset E,
      (∀ p : PrimeSpectrum E, ∃ f ∈ s, f ∉ p.asIdeal) ∧
      ∀ f ∈ s, Nonempty (Module.Basis (Fin r) (Localization.Away f)
        (LocalizedModule.Away f P)))
    (N : Submodule D P) (hspan : Submodule.span E (N : Set P) = ⊤) :
    ∃ b : Module.Basis (Fin r) E P, ∀ i : Fin r, b i ∈ N := by
  sorry

end Module
