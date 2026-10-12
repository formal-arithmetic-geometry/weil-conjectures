/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedTensorComplexCohomologyVanishes
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence

/-! # A cohomology gap for tensoring with a perfect complex

Source: Stacks Project, Derived Categories of Schemes, Tag 09M4, proof,
spectral sequence following the choice of Tor amplitude for the dual perfect complex
(blueprint: lem-sc-perfect-hypercohomology-gap).
-/

@[expose] public section

universe uG wG

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A perfect object of Tor amplitude `[a,b]` tensors a cohomology gap in degrees
`[j-b,j-a]` to vanishing in degree `j`.
Source: Stacks Project, Tag 09M4, spectral sequence in the proof
(blueprint: lem-sc-perfect-hypercohomology-gap).

Proof (the three steps of the node):
1. On affine opens, represent `P` by a bounded strictly perfect complex `Q`
   (def-pc-perfect-complex). Its terms are flat (def-pc-flat-sheaf-modules), so it is
   K-flat (lem-pc-bounded-above-flat-kflat, def-pc-kflat-complex). Restriction commutes
   with tensor and preserves K-flatness, using exact extension by zero for the latter.
   Hence `P ⊗ᴸ L` is represented locally by the total tensor of `Q` with a representative
   of `L` (def-pc-tensor-complex-sheaves). The Tor-amplitude hypothesis gives
   `H^p(Q ⊗ H^q(L)) = 0` whenever `p` is outside `[a,b]`.
2. Filter the total tensor by `Q`-degree. The filtration is finite since `Q` is bounded.
   The filtered-complex spectral sequence (thm-sp-spectral-object-yields) has
   `E₁^{p,q} = Q^p ⊗ H^q(L)` by flatness, and its differential comes from `Q`, giving
   `E₂^{p,q} = H^p(Q ⊗ H^q(L))`. On the diagonal `p+q=j`, this is zero outside `[a,b]`
   by Tor amplitude; inside `[a,b]`, `q=j-p` lies in `[j-b,j-a]`, where `H^q(L)=0`.
   Later pages are subquotients, so all limiting terms on that diagonal vanish.
3. Convergence gives a finite filtration of the degree `j` cohomology with all graded
   pieces zero, hence the cohomology is zero locally. The affine opens cover `X`, so
   vanishing of this cohomology sheaf holds globally. -/
theorem perfect_hypercohomology_gap (X : Scheme.{uG})
    [HasDerivedCategory.{wG} (SheafOfModules.{uG} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wG} (SheafOfModules.{uG} ((moduleRings X.toRingedSpace).over U))]
    (P L : schemeDerivedCategory X) (hP : X.IsPerfect P) (a b : ℤ)
    (hTor : ∀ G : SheafOfModules.{uG} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X P G i)
    (hL : schemeDerivedQCohProperty X L) (j : ℤ)
    (hgap : ∀ q : ℤ, j - b ≤ q → q ≤ j - a →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uG} (moduleRings X.toRingedSpace)) q).obj L)) :
    schemeDerivedTensorComplexCohomologyVanishes X P L j := by
  sorry

end AlgebraicGeometry
