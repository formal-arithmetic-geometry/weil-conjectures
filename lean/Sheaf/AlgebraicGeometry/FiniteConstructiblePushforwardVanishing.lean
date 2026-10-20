/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FiniteMorphismsConstructible

/-!
# Constructibility and vanishing for finite pushforward

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-095r.md`,
order 1774 (blueprint: lem-kun-095r); Stacks Project, Tags 095R and 03QP.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A finite finitely presented morphism between finite-type schemes over a field preserves
constructible module sheaves under direct image, and has zero positive higher direct images.
The coefficient condition is imposed on `Spec k`, so the annihilator is invertible in the
base field. Finite presentation means locally of finite presentation, quasi-compact and
quasi-separated, as in the recorded scheme conventions.

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-095r.md`,
order 1774 (blueprint: lem-kun-095r); Stacks Project, Tags 095R and 03QP.

Proof plan:
1. Apply `fin4-thm-finite-morphisms-constructible` with target `Y`. The target is of finite
   type over `k`, the morphism is finite, and `F` is constructible. The positive annihilator
   is invertible on both schemes because the inverse of its image in `k` maps under the
   structure morphisms to an inverse of the corresponding global section. Thus the
   coefficient convention holds on `X` and `Y`. The cited theorem gives constructibility
   of every nonnegative higher direct image.
2. In degree zero use the module direct image and its left exactness from
   `def-weil-pbc-direct-image`. For an injective resolution `F → I⁰ → I¹ → ⋯`, the kernel
   of `f_*I⁰ → f_*I¹` is the direct image of the kernel, namely `f_*F`. Therefore the
   constructibility in degree zero is precisely constructibility of `f_*F`. In every
   positive degree `fin4-thm-finite-morphisms-constructible` also gives the asserted
   vanishing for the same module sheaf. -/
theorem constructible_lowerStar_and_higherDirectImage_vanishing_of_finite
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f]
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : @Scheme.IsConstructibleEtaleModuleSheaf X Λ _ hcoeff.2.1 F) :
    @Scheme.IsConstructibleEtaleModuleSheaf Y Λ _ hcoeff.2.1
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ∧
    ∀ q : ℤ, 0 < q → IsZero (higherDirectImage Λ f q F) := by
  sorry

end AlgebraicGeometry.Etale
