/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions

import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Classical module sheaves form a weak Serre subcategory

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-cor-pe-classical-derived/sk-cor-pe-classical-derived-weak-serre.md
(blueprint: det-pe-classical-derived-weak-serre).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped ZeroObject

namespace AlgebraicGeometry.ProEtale

/-- Classical sheaves of modules over a discrete commutative coefficient ring contain
zero and are closed under kernels, cokernels and extensions.
Source: current blueprint, main-20261015, sk-cor-pe-classical-derived,
sk-cor-pe-classical-derived-weak-serre.md
(blueprint: det-pe-classical-derived-weak-serre).

Proof, following the seven steps of the node:
1. By det-pe-classical-sheaves-modules, classical module sheaves are the essential
   image of the exact fully faithful comparison inverse image L. In particular,
   zero is classical since L preserves zero.
2. Lift a morphism between classical objects to a morphism of etale module sheaves
   by full faithfulness. Exactness identifies its kernel and cokernel with the
   L-images of the lifted kernel and cokernel, so both are classical.
3. Use def-weil-size-convention and lem-pur-ringed-site-grothendieck-abelian on the
   constant ring sheaves. By lem-sp-grothendieck-enough-injectives both module
   categories have enough injectives. The right adjoint R is additive and left
   exact: def-weil-pbc-site-comparison-morphism describes restriction of sections,
   and def-weil-sheaf-of-modules-category gives sectionwise kernels.
4. For a short exact sequence with classical outer terms G' = L F' and G = L F,
   apply sk-prop-sf-comparison to F'[0]. Its derived unit is invertible.
   lem-sp-derived-functor-single-identification identifies its degree-one
   cohomology on the right with the first right derived functor of R at L F'.
5. Apply degree-one cohomology, as in def-weil-abstract-derived-category. Since
   F'[0] has zero cohomology in degree one, the first right derived functor of R
   vanishes at G'. This also holds after transporting along the chosen isomorphism.
6. The beginning of lem-weil-pbc-derived-functor-long-exact, using the degree-zero
   identification of lem-sp-derived-well-defined, now shows that R takes this
   sequence to a short exact sequence.
7. Apply exact L to that sequence and use naturality of the counit to obtain a
   morphism to the original short exact sequence. Full faithfulness makes the
   unit invertible, and the triangle identity makes the counit invertible on
   L-images. Thus the outer vertical maps are invertible. By
   lem-weil-pbc-short-five-lemma so is the middle counit, showing that the middle
   term is in the essential image of L and hence classical. -/
theorem classicalModule_weakSerre (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    IsClassicalModule (X := X) Λ 0 ∧
      ObjectProperty.IsClosedUnderKernels (IsClassicalModule (X := X) Λ) ∧
      ObjectProperty.IsClosedUnderCokernels (IsClassicalModule (X := X) Λ) ∧
      ObjectProperty.IsClosedUnderExtensions (IsClassicalModule (X := X) Λ) := by
  sorry

end AlgebraicGeometry.ProEtale
