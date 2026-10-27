/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # The largest schematic open of an algebraic space

Source: Stacks Project, Properties of Spaces, Tag 03JH, lemma-subscheme
(blueprint: lem-sfb-space-largest-schematic-open).

The open is a subfunctor of the given algebraic space. Representability means
representability on schemes over the same base, and its point image is the union of
the point images of all representable open subfunctors.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every algebraic space has a largest open subspace represented by a scheme over its
base. Its point image is exactly the union of all such open subspaces' point images.
Source: Stacks Project, Properties of Spaces, Tag 03JH, lemma-subscheme
(blueprint: lem-sfb-space-largest-schematic-open).

Proof:
1. By lem-a1-space-etale-open-image, open subspaces correspond order isomorphically
   to open subsets of the point space. The representable open subspaces form a set.
   Their open point images have an open union O, corresponding to an open subspace J.
2. Each representable open Xi has point image contained in O. The unique factorization
   of lem-a1-space-open-factor-scheme-tests gives Xi -> J -> X. Its scheme tests agree
   with those of Xi -> X, so Xi -> J is representable by open immersions, using
   def-a1-space-open-subspace.
3. For a scheme T -> J, pull back the Xi to open subschemes Ti of T. By
   lem-a1-space-point-open-calculus their point images are the inverse images of |Xi|.
   They cover T because O is their union. The restricted section belongs to Xi(Ti),
   giving precisely the covering condition def-pc-cover.
4. The open subspace J is an algebraic space, hence an fppf sheaf by
   def-a1-space-open-subspace and def-trf-algebraic-space. Zariski covers are fppf
   covers by lem-pc-zariski-coverings-are-fppf. The sheaf equalizer condition of
   def-weil-pbc-sites-and-cohomology gives unique gluing on Zariski covers, namely
   def-pc-zariski-sheaf-property.
5. Apply lem-pc-schemes-criterion to J and the Xi: J is a Zariski sheaf, the Xi are
   representable, their inclusions are open, and they cover J. Thus J is representable
   by a scheme over S.
6. Every representable open is one of the Xi, hence is contained in J, and |J| = O by
   construction. No separation or quasi-compactness is used. If O is empty, all test
   schemes with sections of J are empty and the same covering and gluing argument
   applies, giving the empty scheme. -/
theorem exists_largest_schematic_open {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ J : OpenSubspace X,
      J.val.toFunctor.IsRepresentable ∧
      (∀ A : OpenSubspace X, A.val.toFunctor.IsRepresentable → A ≤ J) ∧
      pointImage J.val.ι =
        ⋃ (A : OpenSubspace X) (_ : A.val.toFunctor.IsRepresentable), pointImage A.val.ι := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
