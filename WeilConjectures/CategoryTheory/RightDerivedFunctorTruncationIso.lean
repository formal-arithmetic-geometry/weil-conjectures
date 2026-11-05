/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage

/-!
# Low-degree cohomology of a right derived functor

Source: Stacks Project, Derived Categories, Lemma 05TC, part (2), with the cone of a morphism
in place of the upper truncation (blueprint: lem-weil-pbc-derived-functor-truncation-iso).

## Main statements

* `CategoryTheory.Functor.isIso_homologyFunctor_rightDerivedFunctorPlus_map`:
  a cohomology isomorphism through degree `n`, monic in degree `n + 1`, remains a cohomology
  isomorphism through degree `n` after applying the right derived functor.
* `CategoryTheory.Functor.isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι`:
  the canonical lower truncation induces an isomorphism on degree-`n` derived cohomology.

`rightDerivedFunctorPlus` is the existing right derived functor on bounded-below derived
categories. It can be computed on bounded-below complexes of injectives, which are
K-injective; thus it realizes the resolution convention of `def-sp-kinjective-bridge`.
`TStructure.t.onPlus` is the induced standard t-structure on the bounded-below subcategory.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

end CategoryTheory.Functor
