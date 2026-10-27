/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Closed immersions of algebraic spaces are proper

Source: Stacks Project, Morphisms of Spaces, Tag 04XZ, lemma-closed-immersion-proper
(blueprint: lem-sfb-space-closed-subspace-proper).

Closed immersions use scheme-test representability; the conclusion uses intrinsic
properness, including universal closedness after every algebraic-space base change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every closed immersion of algebraic spaces over a scheme is proper.
Source: Stacks Project, Morphisms of Spaces, Tag 04XZ, lemma-closed-immersion-proper
(blueprint: lem-sfb-space-closed-subspace-proper).

Proof:
1. For every scheme T over S and map h_T -> X, the closed-immersion hypothesis
   represents Z x_X h_T by a scheme Z_T with closed immersion Z_T -> T.
   Clause (a) of lem-weil-pbc-closed-immersion-proper (scheme Tag 01W5) makes this
   scheme projection proper. This applies to every scheme test, without any
   finite-presentation assumption on the defining ideal.
2. The hypothesis also gives representability by schemes. Apply the reverse
   implication of lem-sfb-space-representable-proper-tests (Tags 03HA and 083R):
   properness of every scheme projection implies intrinsic properness of i,
   namely separatedness, quasi-compactness, local finite type on compatible etale
   scheme charts, and closedness on points after every algebraic-space base change.
   The scheme-test criterion is a theorem, not the definition of the conclusion. -/
theorem mapIsProper_of_isClosedImmersion {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom) :
    MapIsProper i := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
