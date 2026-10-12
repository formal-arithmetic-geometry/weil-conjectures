/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
/-! # Open inverse image preserves injectives

Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- Inverse image along an open immersion preserves injective abelian sheaves.
Source: Stacks Project, Tags 03DI and 03DJ.
(blueprint: lem-pc-open-inverse-image-injectives)

Proof: Identify inverse image along j with sectionwise restriction to its image open.
Exact extension by zero is left adjoint to this restriction. A right adjoint to a
functor preserving monomorphisms preserves injective objects: extend the adjoint
of a morphism across the image of a monomorphism and transpose back. The exact
extension preserves monomorphisms, giving the assertion. Identification with the
image open uses the isomorphism of an open immersion onto its image. For an empty
image the restricted category has only zero objects, which are injective; for
an isomorphism this is invariance of injectivity under an equivalence.
-/
theorem invImage_preservesInjectiveObjects_of_openImmersion {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] : (invImage j).PreservesInjectiveObjects  := by sorry

end AlgebraicGeometry.Scheme.Modules
