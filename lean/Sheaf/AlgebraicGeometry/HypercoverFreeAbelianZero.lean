module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
import Sheaf.Paper.CechNerveFreeHomology

/-! Intermediate degree component for `lem-weil-pbc-hypercover-free-resolution`. -/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SplitEtaleHypercover
/-- This is the degree-zero component of the hypercover free resolution.
Source: Stacks Project, Hypercoverings, Tags 01GC, 01GD, 01GE and 01GW.
(blueprint: lem-weil-pbc-hypercover-free-abelian-zero)

The full resolution is obtained by assembling these degree components with
`quasiIso_iff`; the present theorem records only the indicated component. -/
theorem hypercover_freeAbelian_quasiIsoAt_zero
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) :
    let e := (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _
        (uliftYoneda.{w + 1} ⋙
          (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) AddCommGrpCat.{w + 1}).obj
            AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{w + 1})).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale)))));
    QuasiIsoAt e 0 := by
  sorry

end AlgebraicGeometry.SplitEtaleHypercover
