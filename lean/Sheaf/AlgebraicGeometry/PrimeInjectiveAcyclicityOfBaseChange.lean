/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.TorsionAbelianBaseChange
public import Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicity
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Proper base change implies injective acyclicity

Source: Stacks Project, Tag 0A4B, direction (1) implies (2)
(blueprint: lem-weil-pbc-property-implies-acyclicity).
-/

@[expose] public section

universe u_forward

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- For a proper morphism, base change for torsion abelian sheaves implies injective
acyclicity for every prime. Source: Stacks Project, Tag 0A4B, direction (1) implies (2)
(blueprint: lem-weil-pbc-property-implies-acyclicity).

Fix a prime `r`, a cartesian square, and an injective prime-field module sheaf `I`.
1. Its underlying abelian sheaf is killed by `r`, hence torsion. Apply the specified
exchange isomorphism of `def-weil-pbc-property` to this sheaf in degree zero.
2. By `lem-weil-pbc-injective-module-direct-image-acyclic`, its positive higher direct
images along `f` vanish; degree zero is the ordinary direct image, by
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`.
3. Inverse image is exact (`prop-weil-pbc-inverse-image-exact`), is computed termwise
on the derived category (`def-weil-pbc-derived-inverse-image`), and commutes with
cohomology (`lem-weil-pbc-exact-functor-complex-cohomology`). Thus the source of the
exchange map has zero cohomology in every positive degree.
4. Apply cohomology to the exchange isomorphism. Its target has the same vanishing;
termwise inverse image takes `I[0]` to the pullback sheaf in degree zero, so this is
exactly the higher direct image required by `def-weil-pbc-direct-image`.
5. The square, injective sheaf, and prime were arbitrary, proving every `IA_r(f)` of
`def-weil-pbc-injective-acyclicity-property`. -/
theorem hasAllPrimeInjectiveAcyclicity_of_hasTorsionAbelianBaseChange
    {X Y : Scheme.{u_forward}} (f : X ⟶ Y) [IsProper f]
    (hf : HasTorsionAbelianBaseChange f) : HasAllPrimeInjectiveAcyclicity f := by
  sorry

end AlgebraicGeometry.Etale
