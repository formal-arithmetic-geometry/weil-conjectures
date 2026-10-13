/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison

/-!
# Canonical single-complex shift comparisons

These comparisons isolate the source and unit transport calculations used by
`rightDerivedFunctorPlusUnit_canonical_single_shift`.
-/

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive]

/-- Shift transport of the derived unit on a single object.

Source: Stacks Project, derived.tex, Tag 015J, proof remark (1), and the
canonical single-functor, quotient and homology shift comparisons.
(blueprint: lem-pc-right-derived-single-unit-shift-transport)

Proof: Use the canonical shift isomorphism from single_n X to single_0 X[-n]
in the bounded-below homotopy category. Naturality of rightDerivedFunctorPlusUnit
along this isomorphism, followed by its NatTrans.CommShift equation at -n, moves
the unit to degree zero. The canonical single/quotient identification e converts
the target to the derived single object; its naturality identifies this with the
first factor of c. The right-derived commShift comparison gives the second
factor of c. Apply H^n and use naturality of H₀.shiftIso to move the unit through
the homology shift comparison, giving the third factor of c. On the source,
mapHomotopyCategoryPlusSingleFunctorQhObjIso identifies the mapped single object
with the single object on G(X); compatibility of singleMapHomologicalComplex
with shifts gives d. The degree-zero unit, with its single/quotient identifications,
is precisely rightDerivedPlusSingleUnit. Thus the two paths in this naturality
square are the displayed composites. This uses no cycles projection and no
classical derived-functor comparison. -/
theorem rightDerivedPlusSingleUnit_shift_transport (X : B) (n : ℕ) :
    let S : CochainComplex.Plus B :=
      ⟨(CochainComplex.singleFunctor B (n : ℤ)).obj X, n, inferInstance⟩
    let e : (DerivedCategory.Plus.singleFunctor B n).obj X ≅
        DerivedCategory.Plus.Q.obj S :=
      DerivedCategory.Plus.ι.preimageIso
        ((DerivedCategory.singleFunctorIsoCompQ B n).app X ≪≫
          (DerivedCategory.quotientCompQhIso B).symm.app _)
    let GS := G.mapCochainComplexPlus.obj S
    let H₀ := DerivedCategory.Plus.homologyFunctor C 0
    let RG := G.rightDerivedFunctorPlus
    let c := Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).symm
      (RG ⋙ H₀.shift (n : ℤ)) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor B 0)
        (Functor.isoWhiskerRight (RG.commShiftIso (-(n : ℤ))) (H₀.shift (n : ℤ))) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor B 0 ⋙ RG)
        (H₀.shiftIso (-(n : ℤ)) (n : ℤ) 0 (by ring))
    let d := Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors C).shiftIso (-(n : ℤ)) n 0 (by simp)).symm
      (H₀.shift (n : ℤ)) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
        (H₀.shiftIso (-(n : ℤ)) (n : ℤ) 0 (by ring))
    (DerivedCategory.Plus.homologyFunctor C n).map
      (G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj S)) ≫
      (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map e.inv) ≫
      c.hom.app X =
    (DerivedCategory.Plus.homologyFunctor C n).map
      (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫
      d.hom.app (G.obj X) ≫ H₀.map (G.rightDerivedPlusSingleUnit X) := by
  sorry

end CategoryTheory.Functor
