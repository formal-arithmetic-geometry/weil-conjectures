/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.GeometricFieldProEtaleEvaluation

/-! # Point-unit pasting at terminal evaluation

Source: RefactorInstruction, Sections 4 and 5, coefficient realization and geometric fibers.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedCoefficientUnit

/-- Terminal evaluation transports every section represented by the point unit.

Source: RefactorInstruction, Section 4, lem:XS and prop:pX, and Section 5,
eq:triangle; Bhatt--Scholze, Example 4.1.10.
(blueprint: lem-weil-pbc-condensed-coefficient-point-unit-pasting).

Proof in words: write X = Spec K', Y = Spec K, f = Spec i, and S for the
singleton profinite set. Let qY and qX be the specified structural maps from
Y[S] and X[S] to the final objects. Put A = condensedRingObj Λ Y,
B = condensedRingObj Λ X, and alpha = condensedPullbackHom Λ f.
The evaluation-coherence equation, evaluated on y, identifies restriction of
geometricFieldEvaluationComparison(f)(y) along qX with restrictionComparison(f)
applied to restriction of y along qY. Naturality of alpha along qX moves alpha
from the terminal object to X[S]. The hypothesis identifies the latter restricted
section of A with the point-adjunction unit applied to a.

It remains to identify the point unit followed by restrictionComparison(f) and
alpha on X[S] with the point unit over X. Expand restrictionComparison(f) as the
f-adjunction unit followed by restriction along geometricFieldTestBaseChange(f)
inverse. Naturality of alpha along that inverse moves alpha before restriction.
Expand alpha by condensedPullbackHom_eq. Apply the source-library identity
unit_comp_lowerStar_map_unit_comp_upperStarComp' to f and toSpecZ Y, evaluate it
at profiniteToProEt.obj S, and precompose with the point adjunction unit at a.
Postcompose with restriction along pullbackComp forward; its inverse cancels.
Transport the composite structural map using comp_toSpecZ f. The resulting
composite unit is exactly geometricFieldAbelianPointAdjunction X. This proves
the required equality, with every comparison the specified one.

The argument uses no scalar coordinates and no finiteness or algebraicity
assumption on i. Zero sections and identity embeddings satisfy the same unit and
naturality identities. Finally the singleton structural map qX is invertible over the
algebraically closed
field Kprime by geometric_field_proetale_evaluation. Its presheaf restriction has
inverse given by restriction along qX inverse. Cancel this restriction, using hyprime,
to identify the forward terminal section with yprime. Finally apply the evaluated
inverse of alpha, using Functor.map_comp and the inverse identity of alpha, to obtain
the displayed inverse-comparison equation. -/
theorem terminal_transport (K K' : Type u) [Field K] [IsAlgClosed K]
    [Field K'] [IsAlgClosed K'] (i : K →+* K')
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (a : Λ.obj.obj (op (Profinite.of (ULift.{u, 0} PUnit.{1}))))
    (y : (condensedRingObj Λ (Spec (.of K))).obj.obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K))))))
    (hy : (((geometricFieldAbelianPointAdjunction (Spec (.of K))).unit.app Λ).hom.app
        (op (Profinite.of (ULift.{u, 0} PUnit.{1})))).hom a =
      ((condensedRingObj Λ (Spec (.of K))).obj.map
        (geometricFieldTestFinalMap (Spec (.of K))).op).hom y)
    (y' : (condensedRingObj Λ (Spec (.of K'))).obj.obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K'))))))
    (hy' : (((geometricFieldAbelianPointAdjunction (Spec (.of K'))).unit.app Λ).hom.app
        (op (Profinite.of (ULift.{u, 0} PUnit.{1})))).hom a =
      ((condensedRingObj Λ (Spec (.of K'))).obj.map
        (geometricFieldTestFinalMap (Spec (.of K'))).op).hom y') :
    let f := Spec.map (CommRingCat.ofHom i)
    let E' := sheafToPresheaf (Scheme.ProEt.topology (Spec (.of K'))) Ab.{u + 1} ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of K')))))
    ((geometricFieldEvaluationComparison f Ab).app
      (condensedRingObj Λ (Spec (.of K)))).hom y =
    (E'.map (inv (condensedPullbackHom Λ f))).hom y'  := by sorry

end AlgebraicGeometry.ProEtale.CondensedCoefficientUnit
