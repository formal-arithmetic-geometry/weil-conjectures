/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Yoneda

/-!
# Lifting a set-sheaf equivalence to complete category-valued sheaves

Source: Stacks Project, Sites, Tag 00VR and the preceding Hom-test discussion;
the equivalence-lifting argument is the agent generalization recorded in the DAG
(blueprint: lem-trf-complete-valued-sheaf-equivalence-lift).
-/

@[expose] public section

set_option autoImplicit false

universe v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Restriction that is an equivalence on set-valued sheaves is an equivalence on
sheaves valued in a complete, locally small category. The explicit continuity
proofs below are obtained from finite-limit and covering preservation; continuity
is not an additional hypothesis. `Presheaf.IsSheaf` is exactly the Hom-test of
Stacks Project, Sites, Tag 00VR
(blueprint: lem-trf-complete-valued-sheaf-equivalence-lift).

Proof plan (the six steps of the DAG):
1. Put L = U.op. The category (d downarrow L) is the opposite of (U downarrow d),
   and is v-small. The small pointwise right Kan adjunction gives right adjoints
   T_A and T_set to presheaf restriction, with values the limits over these
   comma categories. Use lem-trf-small-pointwise-right-kan-adjunction.
2. Choose a quasi-inverse E to set-sheaf restriction. Subcanonicity and
   lem-galois-yoneda-hom-bijection identify E(F)(d) with Nat(h_d, E(F)), hence
   with Nat(R_set(h_d), F) by full faithfulness. Such transformations are exactly
   compatible families x_(c,alpha) in F(c), indexed by alpha : U(c) -> d, and
   therefore the pointwise limit defining T_set(F)(d), even for an empty comma
   category. These identifications are natural in d and F. Thus T_set(F) is a sheaf.
3. For every a in A, representable Hom commutes with the right Kan extension by
   lem-trf-hom-right-kan-comparison. Thus H_a(T_A(F)) is isomorphic to
   T_set(H_a(F)), a sheaf by step 2. The Hom-test shows T_A(F) is a sheaf.
   Restriction also preserves sheaves by the same test, so the presheaf
   adjunction restricts to sheaves with the same unit and counit.
4. By lem-coef-adjunction-equivalence-counit-iso the set-valued counit is
   invertible. The counit identity in lem-trf-hom-right-kan-comparison
   identifies H_a of each A-valued counit component with a composite of two
   bijections. Apply lem-coef-joyal-homset-iso-detection at each object to make
   the A-valued counit invertible.
5. Restriction reflects isomorphisms: apply every H_a, reflect through the given
   set-sheaf equivalence, and then use Hom-detection at each object of D.
6. The triangle identity says that the restriction of the unit is the inverse
   of the counit. Step 5 makes the unit invertible as well. The unit and counit
   exhibit T_A as a quasi-inverse of the actual restriction functor. -/
theorem isEquivalence_sheafPushforwardContinuous_of_types
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [PreservesFiniteLimits U] (hU : CoverPreserving J K U)
    (A : Type w) [Category.{v} A] [HasLimitsOfSize.{v, v} A]
    (hset : (@Functor.sheafPushforwardContinuous C _ D _ U (Type v) _ J K
      ((@Functor.isContinuous_iff_coverPreserving C _ D _ U J K
        (flat_of_preservesFiniteLimits U)).mpr hU)).IsEquivalence) :
    (@Functor.sheafPushforwardContinuous C _ D _ U A _ J K
      ((@Functor.isContinuous_iff_coverPreserving C _ D _ U J K
        (flat_of_preservesFiniteLimits U)).mpr hU)).IsEquivalence := by
  sorry

end CategoryTheory.Functor
