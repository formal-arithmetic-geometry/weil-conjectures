/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Abelian.Basic

import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.CategoryTheory.Abelian.Transfer

/-! # Abelianity of quasi-coherent modules on an algebraic stack

Source: Stacks Project, stacks-sheaves.tex, Tag 06WV,
lemma-quasi-coherent-algebraic-stack, part (2)
(blueprint: lem-sfb-stack-qcoh-abelian).

The category is the full subcategory for Mathlib's local-presentation predicate on the
existing big fppf ringed site. No finiteness or Noetherian hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace CategoryTheory

/-- Quasi-coherent modules on an algebraic stack form an abelian category.
Source: Stacks Project, Tag 06WV, lemma-quasi-coherent-algebraic-stack, part (2)
(blueprint: lem-sfb-stack-qcoh-abelian).

Proof:
1. Choose a smooth surjective scheme atlas using `def-sfb-algebraic-moduli-stack`.
   By `lem-sfb-stack-chartwise-smooth-etale-calculus` it is flat and locally of finite
   presentation. Clause (2) of `lem-sfb-fppf-groupoid-stack-presentations` gives the
   self-relation groupoid with flat projections. Its relation is an algebraic space;
   it need not be a scheme.
2. By `lem-sfb-smooth-atlas-module-descent`, restriction identifies quasi-coherent
   modules with pairs (M, delta : p1* M ≅ p2* M) satisfying the descent cocycle.
   Replacing delta by alpha = delta inverse turns delta13 = delta23 delta12 into
   alpha13 = alpha12 alpha23, and turns deltaN p1*v = p2*v deltaM into
   p1*v alphaM = alphaN p2*v. These are precisely the conventions of
   `lem-sfb-flat-space-groupoid-abelian`; flatness of both projections makes that
   category abelian, also for arbitrary modules and algebraic-space relations.
3. The full module subcategory is preadditive by sectionwise addition and distributivity.
   Transport finite products through a quasi-inverse H of the equivalence E: the product
   of F_j is H(product E(F_j)). Full faithfulness and the inverse isomorphisms give its
   universal property. The empty family gives a terminal object as well.
4. Apply `lem-sfb-preadditive-abelian-equivalence`, namely Mathlib's
   `abelianOfEquivalence`, to this preadditive category with finite products and the
   equivalence from step 2. No finiteness assumption enters. This asserts abelianity of
   the full subcategory; it does not assert exactness of its inclusion. -/
theorem stack_qcoh_abelian {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F) :
    Nonempty (Abelian (SheafOfModules.isQuasicoherent.{max (u + 1) v w}
      (moduliModuleRings F hF.1.1)).FullSubcategory) := by
  sorry

end CategoryTheory
