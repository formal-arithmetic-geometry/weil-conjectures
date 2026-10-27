/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated

/-! # Cohomological approximation for a tensor of two morphisms

Source: Stacks Project, More on Algebra, Tag 0DJE, proof of (1), tensor approximation
assertion, expanded by the cone-triangle argument.
(blueprint: lem-trf-derived-tensor-approximation-comparison)

The tensor is the existing K-flat monoidal tensor on the derived category of modules.
Its K-flat representative comparisons are `DerivedCategory.QObjTensorQObjIsoOfKFlatLeft`
and `DerivedCategory.QObjTensorQObjIsoOfKFlatRight`.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

/-- Tensoring two cohomological approximations gives cutoff `max (n + b) (a + m)`,
including a surjection at the cutoff.
Source: Stacks Project, More on Algebra, Tag 0DJE, proof of (1), omitted tensor estimate.
(blueprint: lem-trf-derived-tensor-approximation-comparison)

Proof:
1. Complete `α` and `β` to distinguished cone triangles using TR1
   (`def-weil-abstract-derived-category`, `def-weil-triangulated-category`). The long exact
   cohomology sequence (`lem-sf-derived-homology-long-exact`) shows their cones vanish in
   degrees at least `n` and `m`: the incoming cohomology map is surjective and the next
   cohomology map is injective. Thus the cone upper bounds are `n - 1` and `m - 1`.
2. Choose flat-term K-flat representatives of `Q` and `K` (`lem-pc-kflat-resolution`).
   Exact fixed tensor descent (`lem-weil-pbc-kflat-fixed-tensor-triangulated`) tensors
   the first cone triangle by `Q` and the second by `K`. The normalized comparisons
   identify their first arrows with `α ⊗ 1` and `1 ⊗ β` for the existing K-flat tensor
   (`lem-pc-derived-tensor-second-factor-functor`).
3. Apply `lem-weil-pbc-source-derived-tensor-upper-bound` to the two tensor cones,
   with bounds `(n - 1, b)` and `(a, m - 1)`. They vanish in degrees at least
   `n + b` and `a + m`, respectively, hence in degrees at least their maximum.
4. In each tensor triangle, the long exact sequence has outside terms `H^(i-1)(cone)`
   and `H^i(cone)`. Both vanish above the maximum, giving an isomorphism; the right
   term vanishes at the maximum, giving a surjection.
5. Bifunctoriality identifies the composite of the two first arrows with `α ⊗ β`.
   Cohomology preserves composition, so the two isomorphism and surjectivity conclusions
   compose. No freeness, pseudo-coherence, lower bound or finite Tor dimension is used. -/
theorem derivedTensor_approximation_comparison
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {P K Q L : DerivedCategory (ModuleCat.{u} R)}
    (α : P ⟶ K) (β : Q ⟶ L) (n m a b : ℤ)
    (hα : ∀ i : ℤ, n < i → IsIso ((homologyFunctor (ModuleCat.{u} R) i).map α))
    (hαn : Epi ((homologyFunctor (ModuleCat.{u} R) n).map α))
    (hβ : ∀ i : ℤ, m < i → IsIso ((homologyFunctor (ModuleCat.{u} R) i).map β))
    (hβm : Epi ((homologyFunctor (ModuleCat.{u} R) m).map β))
    (hK : ∀ i : ℤ, a < i → IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj K))
    (hQ : ∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj Q)) :
    (∀ i : ℤ, max (n + b) (a + m) < i →
      IsIso ((homologyFunctor (ModuleCat.{u} R) i).map (α ⊗ₘ β))) ∧
    Epi ((homologyFunctor (ModuleCat.{u} R) (max (n + b) (a + m))).map (α ⊗ₘ β)) := by
  sorry

end DerivedCategory
