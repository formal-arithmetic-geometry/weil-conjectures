/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# Global sections under field extension in dimension zero

Source: the degree-zero argument of blueprint lem-weil-pbc-zero-dimensional-field-extension.
(blueprint: lem-weil-pbc-zero-dimensional-pullback-global-sections).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Pullback on global sections of an abelian etale sheaf is bijective for a
 zero-dimensional finite-type scheme over an algebraically closed field.
 Source: blueprint lem-weil-pbc-zero-dimensional-field-extension, proof steps 1 and 4;
 Stacks Project, Tags 03Q1 and 0GJA.
 (blueprint: lem-weil-pbc-zero-dimensional-pullback-global-sections).

 Proof: The source has finitely many closed points with residue field k, and after
 extending k to k' the projection gives a bijection of these point sets, by
 lem-weil-pbc-zero-dimensional-base-change-points. Choose an algebraically closed
 geometric point above each point of the base change and compose it with the projection.
 The germ maps identify global sections on both schemes with products of these stalks,
 by lem-weil-pbc-zero-dimensional-sections-stalks. Inverse image identifies each target
 stalk with the corresponding source stalk, compatibly with germs of sections, by
 lem-weil-pbc-inverse-image-stalk-germ. Consequently the global sections pullback is,
 under these product identifications, the product of the stalk isomorphisms reindexed
 along the point bijection. It is therefore bijective. The empty scheme gives empty
 products and is covered by the same argument. Neither torsion nor reducedness is used. -/
theorem bijective_globalSectionsUpperStarMap_of_dim_zero {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] (hC : topologicalKrullDim C ≤ 0)
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} ι' F) := by sorry

end AlgebraicGeometry.Etale
