/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechCoefficientMap

/-! # The fixed additive coefficient augmentation on vertical columns

Source: Stacks Project, Tags 03P2 and 01EQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Each fixed coefficient map augments its vertical resolution column by a
quasi-isomorphism when the tuple intersections are affine.
Source: Stacks Project, Theorem 59.22.4 (Tag 03P2), affine acyclicity, and
Lemma 20.11.2 (Tag 01EQ), the augmented vertical columns.
(blueprint: lem-pbc-additive-cech-coefficient-columns)

Proof: Fix n. For each tuple y the underlying open is the categorical product
of U(y l), equal to their infimum by the universal property in the poset of
opens. Thus hU makes this open affine. Evaluating I on this open computes
right-derived evaluation of the additive structure sheaf. Its positive
cohomology vanishes by affine quasi-coherent etale acyclicity: identify the
unit's tensor-section sheaf with additive structural sections using the
natural unit coordinates, apply finite affine etale Cech vanishing and the
Cech vanishing criterion. Left exactness of evaluation identifies degree-zero
homology with additive sections, through the evaluated resolution augmentation.
The inverse of restrictFunctorΓ is the canonical identification from ordinary
unit sections with these sections, including the ULift. Take the product over
y. Products in abelian groups are exact, so they preserve these homology
calculations, and forgetting scalars and lifting the universe commute with the
finite products in the ordinary Cech term. The resulting degree-zero map is
exactly additiveCechCoefficientMap, by its projections. Its composition with
the next differential vanishes by additiveCechCoefficientMap_vertical, so
fromSingle₀Equiv constructs the augmented column map. It is an isomorphism on
homology in degree zero and between zero objects in every positive degree.
There is no covering hypothesis: the reasoning is on individual affine
intersections. Empty tuple families give zero columns and empty intersections
have zero sections; the same proof applies in degree zero and to repeated opens. -/
theorem additiveCechCoefficientMap_column_quasiIso
    (X : Scheme.{u}) [X.IsSeparated] {ι : Type u} [Finite ι]
    (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    QuasiIso
      ((CochainComplex.fromSingle₀Equiv
        ((etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).X n)
        ((additiveCechCoefficientComplex U).X n)).symm
          ⟨additiveCechCoefficientMap U I n, additiveCechCoefficientMap_vertical U I n⟩) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
