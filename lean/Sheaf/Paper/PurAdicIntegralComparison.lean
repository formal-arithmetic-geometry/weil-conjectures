/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.Paper.PurAdicLineSystemData

/-! # Semilinear comparison of locally based integral towers

Source: the integral twist paragraph of
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`.
(blueprint: lem-pur-adic-integral-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The projection-normalized integral module comparison exists over the specified
coefficient comparison. No naturality in the coefficient index is assumed or concluded.
Source: the integral twist paragraph of the blueprint coefficient-twists proof;
Stacks, Sites, Tag 03CF, lemma-localize-morphism.
(blueprint: lem-pur-adic-integral-comparison).

Proof: Fix i. The supplied cofinal identifications make the full ring limit
also present the subsequence ring limit. The given projection equations
for a.integral and a.full show that the comparison from L of that ring limit to
the limit of its inverse image is invertible: compose it with the levelwise
ring isomorphisms and test on projections to obtain a.integral.
On each member of the one common cover, the compatible bases identify the module
tower with this ring tower. The slice inverse-image comparison of Tag 03CF
transports these bases to the target slice. Both slice restriction functors
preserve tower limits. Testing on projections shows that the localized module
comparison is conjugate to the invertible ring comparison. The images of the
cover cover the target terminal object, so local bijectivity makes the module
comparison invertible globally. Compose with the levelwise c comparisons.
On the product of the ring and module sheaves, test the scalar equation on every
projection; it follows from projection_smul and the graph equations for c and a.
The additive equation is proved in the same way. These equations lift the
underlying isomorphism to an isomorphism from the specified inverse image of A.integral.M i
to B.integral.M i. The inverse is linear by the same equations. This construction uses
only the comparison's projections, which are exactly the displayed formula. -/
theorem purAdicIntegralComparison_exists
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (U : C ⥤ D) [PreservesFiniteLimits U]
    (hUcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map U ∈ K (U.obj X))
    [U.IsContinuous J.toGrothendieck K.toGrothendieck]
    (L : Sheaf J.toGrothendieck (Type w) ⥤ Sheaf K.toGrothendieck (Type w))
    (adj : L ⊣ U.sheafPushforwardContinuous (Type w) J.toGrothendieck K.toGrothendieck)
    [PreservesFiniteLimits L]
    {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J.toGrothendieck I e)
    (B : PurAdicLineLimits.{w} K.toGrothendieck I e)
    (c : PurAdicPairComparison L A.levels B.levels)
    (a : PurAdicCoefficientComparison L A B c)
    (bases : PurAdicLineLocallyBased J A)
    (hA : PurAdicCofinalRestriction A) (hB : PurAdicCofinalRestriction B) :
    ∀ i : I, ∃ ci : (a.integral i).modules.obj (A.integral.M i) ≅ B.integral.M i,
      ∀ n : ℕ,
        (purAdicModuleIso L A.integral B.integral i (a.integral i) ci).hom ≫
            (sheafCompose K.toGrothendieck (forget AddCommGrpCat.{w})).map
              ((B.pπ i).app (op n)) =
          L.map ((sheafCompose J.toGrothendieck (forget AddCommGrpCat.{w})).map
            ((A.pπ i).app (op n))) ≫
              (purAdicModuleIso L A.levels B.levels (i, op n) (c.a _) (c.c _)).hom := by
  sorry

end CategoryTheory
