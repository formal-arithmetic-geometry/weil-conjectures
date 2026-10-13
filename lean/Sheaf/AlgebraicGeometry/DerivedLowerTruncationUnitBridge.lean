/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # The bottom derived unit on a lower-truncated complex

Source: Stacks Project, Tag 05TC (2) and the single-object calculation of
Tags 015A, 05TH and 05TI.
(blueprint: lem-sc-derived-lower-truncation-unit-bridge).
-/

@[expose] public section

universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The derived edge map factors through the underived lower truncation, and
its bottom-degree comparison there is invertible. This concerns the derived
unit and localization only; it contains no cycle-class or homology quotient map.

Source: Stacks Project, Tag 05TC (2); Tags 015A, 05TH, 05TI, and naturality of
localization and of the right-derived unit.
(blueprint: lem-sc-derived-lower-truncation-unit-bridge).

Proof: Put K = truncGE n I. In the derived category, QK is the good lower
truncation of QI: the short exact truncation sequence gives a distinguished
triangle whose first object is strictly below n and whose last object is at
least n. Uniqueness of the truncation triangle gives a canonical isomorphism
QK to tauGE n QI, commuting with the projection from QI. Compose its inverse
with the quotient-to-homotopy factor isomorphism to identify Q_h(PK) with
this lower truncation.

The derived unit at K is an isomorphism on H^n. To see this with the actual
unit, upper-truncate K at n. Negative vanishing (Tag 05TC) makes the derived
upper-truncation inclusion invertible on H^n. Double truncation is H^n(K)
placed in degree n. Shift it to degree zero. The derived unit on a single
object is the canonical F to R^0 F map, computed by the augmentation of an
injective resolution. F preserves the augmentation kernel, so this map is
invertible. Naturality of the unit for the upper-truncation inclusion and
the double-truncation projection transports invertibility back to K. No
choice of an arbitrary bottom cohomology isomorphism is involved.

Define d by the inverse homotopy and derived homology factor isomorphisms
for F(K), followed by H^n of the unit at K and by H^n of RF of the canonical
isomorphism Q_h(PK) to tauGE n QI. Each factor is invertible, hence so is d.
Naturality of the unit at P(I to K), naturality of the homology factor
isomorphisms, and the commuting truncation-projection triangle identify
e H^n(U) H^n(q) with H^n(F(I to K)) d. The argument only uses that K is
strictly zero below n, so all integers n, unbounded I, and zero complexes
satisfy the same calculation. -/
theorem derived_lower_truncation_unit_bridge
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (I : CochainComplex C ℤ) (n : ℤ) :
    let J := (F.mapHomologicalComplex (.up ℤ)).obj I
    let H := DerivedCategory.homologyFunctor D n
    let e := ((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app J).symm ≪≫
      ((DerivedCategory.homologyFunctorFactorsh D n).app
        ((HomotopyCategory.quotient D (.up ℤ)).obj J)).symm
    let U := F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)
    let q := F.rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso C).hom.app I ≫
        (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I))
    ∃ d : ((F.mapHomologicalComplex (.up ℤ)).obj (I.truncGE n)).homology n ≅
        H.obj (F.rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj I))),
      e.hom ≫ H.map U ≫ H.map q =
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (.up ℤ)).map (I.πTruncGE n)) n ≫ d.hom := by sorry

end AlgebraicGeometry
