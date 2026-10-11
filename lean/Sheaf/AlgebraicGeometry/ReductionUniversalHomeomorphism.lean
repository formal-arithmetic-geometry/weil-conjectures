/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# The reduction is a universal homeomorphism

Source: literature/stacks-project/morphisms.tex, Lemma 054M.
(blueprint: lem-weil-pbc-reduction-universal-homeomorphism).
-/

universe u

namespace AlgebraicGeometry

/-- The reduction is reduced and its canonical map is a surjective closed immersion
and a universal homeomorphism. The proof follows Stacks Lemma 054M and Lemma 01J3.
Source: Stacks Project, Morphisms, Lemma 054M; Schemes, Lemma 01J3 / Definition 01J4.
(blueprint: lem-weil-pbc-reduction-universal-homeomorphism).
Proof:
1. By def-weil-pbc-scheme-reduction the map is the nilradical closed immersion
   (def-weil-closed-immersion). Every prime contains the nilradical, so its support
   is all of X and the map is surjective (def-weil-surjective-morphism).
   A closed embedding onto all of X is a homeomorphism.
2. On an affine open Spec R (def-weil-affine-spectrum), the inverse image is
   Spec (R / nilradical R). If a class is nilpotent, a power of its representative
   belongs to the nilradical, so a further power is zero; the representative itself
   is therefore in the nilradical. The quotient is reduced. Apply
   lem-weil-pbc-affine-scheme-reduced-iff on this affine cover, and hence all local
   rings are reduced (def-pc-reduced-scheme), as in Stacks 01J3 for the full subset.
3. For every morphism X' → X, its fibre product (def-pc-fibre-product) projection
   is a closed immersion by lem-weil-pbc-closed-immersion-base-change and surjective
   by lem-weil-pbc-surjective-base-change. Its underlying closed embedding is
   surjective and therefore a homeomorphism. This is exactly
   def-weil-universal-homeomorphism. -/
theorem reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism
    (X : Scheme.{u}) :
    IsReduced X.nilradical.subscheme ∧
      IsClosedImmersion X.nilradical.subschemeι ∧
        Surjective X.nilradical.subschemeι ∧
          (topologically IsHomeomorph).universally X.nilradical.subschemeι := by
  sorry

end AlgebraicGeometry
