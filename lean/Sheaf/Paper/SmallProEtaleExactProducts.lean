/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.FieldScalarStrictLimitData
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact

/-! # Exact countable products on a chosen small model of the pro-etale site -/

@[expose] public section
set_option autoImplicit false
universe u t
open CategoryTheory CategoryTheory.Limits
open SheafOfModules SheafOfModules.RingedTensor
namespace SheafOfModules

/-- Exact countable products for module sheaves on any specified small pro-etale model.
Source: blueprint field-extension-towers proof (1); Stacks Tag 0941 and
lem-weil-proetale-countable-products-exact.
(blueprint: lem-sp-small-proetale-exact-products).

Proof: Transport the ring sheaf and its modules along the equivalence of sites e.
When the ring universe is smaller than that of the displayed pro-etale site, first
lift rings and modules to a common universe; equivalence with the small model
identifies the lifted products with lifts of the small products. Sheaf conditions
and module operations are preserved by the site equivalence. Universe lifting
preserves products and preserves and reflects local surjectivity, hence epimorphisms
of module sheaves. Apply countableProducts_exact to the lifted ring and lifted
epimorphisms; reflect the resulting product epimorphism back to the small universe.
In an abelian category the product functor is left
exact, and preservation of epimorphisms makes it right exact. This is the asserted
HasExactLimitsOfShape instance. Empty sites and zero rings satisfy the same argument. -/
theorem smallProEtaleExactProducts {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (T : AlgebraicGeometry.Scheme.{t})
    (e : C ≌ T.ProEt)
    (hJ : J = e.functor.inducedTopology (AlgebraicGeometry.Scheme.ProEt.topology T))
    (R : Sheaf J CommRingCat.{u}) :
    HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u} (ringSheaf R)) := by sorry

end SheafOfModules
