module

public import Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive]

/-- Transport of the single-complex unit from degree n to degree zero.
Source: Stacks Project, derived.tex, Tag 015J, proof, remark (1), and
`Functor.commShift_rightDerivedFunctorPlusUnit`.
(blueprint: lem-pc-right-derived-canonical-single-unit-shift)

Proof: Identify the degree-n single object with the shift by -n of the degree-zero
single object using singleFunctors.shiftIso. Apply naturality of the derived unit
along this identification and its NatTrans.CommShift equation at -n. Apply H^n
and the homology shift isomorphism H^n(K[-n]) = H^0(K). The three isomorphisms
in c are exactly these target transports. On the source, naturality of
homologyFunctorObjQIso and the single-complex homology comparison identify the
transported cycles projection with iCycles followed by the sole-term coefficient
identification and singleFunctorCompHomologyFunctorIso 0 inverse. The remaining
morphism is H^0 of rightDerivedPlusSingleUnit, hence the displayed degree-zero
unit homology map. For n=0 the shift unit laws give the same equation; zero X
requires no special choice. This calculation uses only additivity, and does not
use either the classical derived-functor comparison or left exactness. -/
theorem rightDerivedFunctorPlusUnit_canonical_single_shift (X : B) (n : ℕ) :
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
    GS.obj.homologyπ n ≫ (DerivedCategory.Plus.homologyFunctorObjQIso GS n).inv ≫
      (DerivedCategory.Plus.homologyFunctor C n).map
        (G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj S)) ≫
      (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map e.inv) ≫
      c.hom.app X =
    GS.obj.iCycles n ≫
      G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n X).hom ≫
      G.rightDerivedPlusSingleUnitHomology X := by
  sorry

end CategoryTheory.Functor
