/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist

/-!
# Closed-immersion right adjoint before restriction

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-sf-existence/lem-exc-closed-ambient.md,
node lem-exc-closed-ambient, order 1803
(blueprint: lem-exc-closed-ambient).
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Closed direct image has a right adjoint on the ordinary, unbounded derived categories.
The open complement is canonical and is not extra input to this existence assertion.
Source: blueprint smooth-purity, sk-prop-sf-existence, node order 1803
(blueprint: lem-exc-closed-ambient).

Proof:
1. For the open complement j put Gamma_Z N = ker(N → j_* j^* N). Geometric-stalk
   conservativity (lemma-weil-pbc-geometric-stalk-conservative) identifies sheaves
   supported on Z with sheaves on Z via the exact fully faithful i_*. Its inverse
   is i^* (def-weil-pbc-inverse-image). Every map i_* M → N factors uniquely through
   Gamma_Z N, giving the sheaf adjunction i_* ⊣ i^* Gamma_Z.
2. Resolve by K-injectives with injective terms
   (prop-weil-pbc-kinjective-resolutions-exist). Since i_* is exact, its right
   adjoint preserves K-injectives: Hom from an acyclic complex stays acyclic by the
   termwise adjunction. Computing derived Hom into those resolutions gives the
   ordinary derived adjunction. Closed i_* is already exact, so its derived functor
   (def-weil-pbc-direct-image) is i_* applied termwise. No constructibility is used. -/
@[instance]
theorem isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion
    (A : Type (u + 1)) [Ring A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    (R(lowerStar (ModuleCat.{u + 1} A) i)).IsLeftAdjoint := sorry

end AlgebraicGeometry.Etale
