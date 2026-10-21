/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit

import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic

/-!
# Bounds for derived limits with epimorphic top cohomology

Source: Stacks Project, Tag 0947, `proposition-enough-weakly-contractibles`, (5)-(7)
and its proof, specialized to the small pro-etale site
(blueprint: lem-sf-bounded-epimorphic-top-derived-limit).

The index `n : ℕ` denotes the positive level `n + 1` of the source tower.
The coefficient sheaf is written as a sheaf of rings with sectionwise commutativity;
this retains exactly the given ring and module structures. A derived limit is any
object satisfying the existing Roos-triangle property, without a chosen cone model.
-/

@[expose] public section

set_option autoImplicit false

universe t u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEt

/-- A strict tower with cohomology in `[a,b]` and epimorphic top-cohomology
transitions has every derived limit cohomologically in the same interval.

Source: Stacks Project, Tag 0947, `proposition-enough-weakly-contractibles`, (5)-(7)
and its proof (blueprint: lem-sf-bounded-epimorphic-top-derived-limit).

Proof plan:
1. By det-pe-products-derived, the termwise product represents the product of the
   localized complexes and its cohomology is the product of their cohomologies.
   The universal property in def-weil-category-product identifies any supplied
   product with that model, compatibly with all projections. Hence the Roos map
   on degree-j cohomology is the actual `1 - T_j` on the product of H^j(P_n).
   This uses the localization and cohomology of def-weil-abstract-derived-category.
2. Apply lem-sf-derived-homology-long-exact to the supplied distinguished triangle
   of def-weil-derived-limit. Writing V_j for the product of H^j(P_n), obtain
   V_(j-1) -> V_(j-1) -> H^j(L) -> V_j -> V_j, with arrows `1 - T` on the V's.
3. For j < a or j > b + 1, both adjacent V's vanish by the common bounds.
   A product of zero objects is zero by its universal property, and exactness
   then forces H^j(L) to vanish.
4. Apply the first assertion of det-pe-milnor-epimorphic to the module-sheaf
   tower H^b(P_n), using exactly the assumed epimorphy. It makes `1 - T_b`
   epic. Reindexing the positive levels by ℕ changes no consecutive transition.
5. At j = b + 1, V_(b+1) = 0. The connecting map out of V_b annihilates the
   epic map `1 - T_b`, so it is zero. Exactness says its image is all of
   H^(b+1)(L); consequently that object is zero as well. No degreewise
   epimorphy of the strict tower maps is used. -/
theorem bounded_epimorphic_top_derivedLimit
    (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    (_hcomm : ∀ U : X.ProEtᵒᵖ, ∀ r s : R.obj.obj U, r * s = s * r)
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)]
    (P : ℕ → CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ)
    (τ : ∀ n : ℕ, P (n + 1) ⟶ P n)
    [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (P n))]
    (L : DerivedCategory (ringedSiteModules.{max u (t + 1)} R))
    (_hL : IsDerivedLimit (K := fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (P n))
      (fun n : ℕ ↦ DerivedCategory.Q.{w}.map (τ n)) L)
    (a b : ℤ) (_hab : a ≤ b)
    (_hP : ∀ (n : ℕ) (j : ℤ), j < a ∨ b < j → IsZero ((P n).homology j))
    (_htop : ∀ n : ℕ, Epi (HomologicalComplex.homologyMap (τ n) b)) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (ringedSiteModules.{max u (t + 1)} R) j).obj L) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
