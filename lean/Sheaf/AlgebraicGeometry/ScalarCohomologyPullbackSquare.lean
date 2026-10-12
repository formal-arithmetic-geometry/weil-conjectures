/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Scalar cohomology pullback along a commutative square

Source: Stacks Project, Tags 0097 and 01FD.
(blueprint: lem-sc-scalar-cohomology-pullback-square).
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Two successive scalar pullbacks agree around a commutative square, after
the normalized composition comparison on their coefficient modules.
Source: Stacks Project, Tags 0097 and 01FD; Step 8 of lem-sc-picard-kunneth-qcoh (Tag 0BED).
(blueprint: lem-sc-scalar-cohomology-pullback-square).

Proof: The comparison of Tag 0097 is the unique isomorphism of left adjoints
intertwining their units. The definition scalarPullbackCompIso uses precisely this
isomorphism for the normalized tensor-pullback adjunctions. Consequently its
inverse identifies the successive unit with the unit of the composite morphism.
Apply this on both paths a then b, and c then d. The equality h identifies the two
composites; scalarPullbackSquareIso is the first inverse comparison followed by
this equality and the second comparison. Thus it intertwines the two composite
coefficient maps. The resolution construction of cohomology pullback in Tag 01FD
respects successive coefficient maps: compose the resolution lifts over the units;
any two such lifts are homotopic, so their maps on cohomology agree. The natural
injective-resolution comparison to Ext used by scalarCohomologyExtEquiv transports
these maps to scalarCohomologyPullback, whose inverse-image coefficient is adjoint
to the same normalized unit. Transporting the square equality back identifies its
coefficient change with scalarCohomologyMap. Proof irrelevance removes dependence
on the chosen proofs ha, hb, hc, hd and h. Identity morphisms give the unit
comparison, degree zero gives composition of section pullbacks, and zero modules
or empty schemes give zero maps. No quasi-coherence or compactness is needed.
-/
theorem scalarCohomologyPullback_square
    (k : Type w) [Field k] (A B C D : Scheme.{w})
    (fA : A ⟶ Spec (CommRingCat.of k)) (fB : B ⟶ Spec (CommRingCat.of k))
    (fC : C ⟶ Spec (CommRingCat.of k)) (fD : D ⟶ Spec (CommRingCat.of k))
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (ha : a ≫ fB = fA) (hb : b ≫ fD = fB)
    (hc : c ≫ fC = fA) (hd : d ≫ fD = fC) (h : a ≫ b = c ≫ d)
    (F : D.Modules) (n : ℕ) (x : scalarCohomology fD F n) :
    scalarCohomologyMap fA (scalarPullbackSquareIso a b c d h F).hom n
        (scalarCohomologyPullback fB fA a ha ((tensorPullback b).obj F) n
          (scalarCohomologyPullback fD fB b hb F n x)) =
      scalarCohomologyPullback fC fA c hc ((tensorPullback d).obj F) n
        (scalarCohomologyPullback fD fC d hd F n x) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
