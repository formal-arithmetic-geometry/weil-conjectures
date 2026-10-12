/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.ConstantCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Cohomology sheaves of a pro-étale derived complex

Blueprint `def-weil-derived-cohomology-sheaves`. For a scheme `Y`, a commutative ring `Λ`, a
complex `K ∈ D(Y_proét, Λ) = DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat Λ))`
(`def-weil-pbc-proetale-modules`) and `r : ℤ`, the `r`-th cohomology sheaf `ℋ^r(K)` is
`(DerivedCategory.homologyFunctor _ r).obj K`, the cohomology functor of the canonical
t-structure `DerivedCategory.TStructure.t`. This is not given a definition of its own; the
facts of the blueprint node are the generic Mathlib statements, recorded below as `example`s:

* `K` lies in the nonpositive part iff `ℋ^r(K) = 0` for `r > 0` (`DerivedCategory.isLE_iff`),
  and in the nonnegative part iff `ℋ^r(K) = 0` for `r < 0` (`DerivedCategory.isGE_iff`);
* `ℋ^r` is computed on any representing complex (`DerivedCategory.homologyFunctorFactors`), so
  it is invariant under quasi-isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] (Y : Scheme.{u})

/-- `def-weil-derived-cohomology-sheaves`: the `r`-th cohomology sheaf of `K ∈ D(Y_proét, Λ)`. -/
noncomputable example
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ) :=
  (DerivedCategory.homologyFunctor _ r).obj K

/-- `def-weil-derived-cohomology-sheaves`: the nonpositive part of the standard t-structure. -/
example
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    K.IsLE 0 ↔ ∀ r : ℤ, 0 < r → IsZero ((DerivedCategory.homologyFunctor _ r).obj K) :=
  DerivedCategory.isLE_iff K 0

/-- `def-weil-derived-cohomology-sheaves`: the nonnegative part of the standard t-structure. -/
example
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    K.IsGE 0 ↔ ∀ r : ℤ, r < 0 → IsZero ((DerivedCategory.homologyFunctor _ r).obj K) :=
  DerivedCategory.isGE_iff K 0

/-- `def-weil-derived-cohomology-sheaves`: `ℋ^r` is the cohomology of a representing complex. -/
noncomputable example
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ) (r : ℤ) :
    (DerivedCategory.homologyFunctor _ r).obj (DerivedCategory.Q.obj K) ≅ K.homology r :=
  (DerivedCategory.homologyFunctorFactors _ r).app K

end AlgebraicGeometry.ProEtale
