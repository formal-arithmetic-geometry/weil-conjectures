/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.Paper.DerivedHomMayerVietoris
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Products in the derived category of a ringed space

Source: Stacks Project, Injectives, Tag 07D9 (blueprint: lem-pc-ringed-space-derived-products).
-/

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSpace

/-- The derived category of modules on a ringed space has products indexed by every set
(the abelian structure is Mathlib's `SheafOfModules.instAbelian`).
Source: Stacks Project, Injectives, Tag 07D9 (blueprint: lem-pc-ringed-space-derived-products).
Proof:
1. Regard the opens of `X` as a small site with structure sheaf `moduleRings X`.
   By `prop-pur-kinjective-resolutions-exist` its module-sheaf category is Grothendieck
   abelian and every complex has a K-injective resolution (`def-pur-kinjective-complex`).
   Choose representatives of the objects `K_i` and resolutions `K_i → I_i`.
2. Module sheaves have sectionwise products. Form the termwise product complex `P` of
   the `I_i`, with its projections. Maps and homotopies into `P` are exactly families
   of maps and homotopies into the factors, so `Hom_K(L, P) = ∏ i, Hom_K(L, I_i)`.
   For acyclic `L` every factor vanishes; hence `P` is K-injective by
   `def-pur-kinjective-complex` (Stacks, Derived Categories, Tag 070L).
3. By `lem-weil-pbc-kinjective-hom-derived`, maps into `P` and the `I_i` in the derived
   category are the same as maps in the homotopy category. Thus the projections induce
   `Hom_D(L, P) = ∏ i, Hom_D(L, K_i)`, the product universal property of
   `def-weil-category-product`. Specializing the indexing set to a countable set gives
   the final assertion.
-/
theorem derivedProducts (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))] :
    HasProducts.{u} (DerivedCategory (SheafOfModules.{u} (moduleRings X))) := by
  sorry

end AlgebraicGeometry.RingedSpace
