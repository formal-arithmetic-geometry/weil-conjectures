module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Data.Fintype.Order
public import Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels
public import WeilConjectures.AlgebraicGeometry.FiniteFamilyJointSurjectivityStage
public import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! Declarations of ours that lived in the upstream file `WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# Finite-presentation data at an inverse limit

Source: Stacks Project, Limits, Tags 01ZM, 07RP and 07RR
(blueprint: lem-weil-pbc-etale-finite-data-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem pullbackComp_inv_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (W : Over Z) :
    ((Over.pullbackComp f g).inv.app W).left ≫ pullback.fst W.hom (f ≫ g) =
      pullback.fst (pullback.snd W.hom g) f ≫ pullback.fst W.hom g := by
  have H := conjugateEquiv_counit ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapPullbackAdj (f ≫ g)) (Over.mapComp f g).hom W
  simpa [Over.pullbackComp, Adjunction.comp_counit_app] using
    congrArg (fun k ↦ k.left) H

private theorem comparison_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) (W : Over Z) :
    ((((Over.pullbackComp f g).symm ≪≫
      eqToIso (congrArg (fun t : X ⟶ Z ↦ Over.pullback t) h)).app W).hom).left ≫
        pullback.fst W.hom k =
      pullback.fst (pullback.snd W.hom g) f ≫ pullback.fst W.hom g := by
  subst k
  simpa using pullbackComp_inv_fst f g W

set_option linter.unusedVariables false in
end AlgebraicGeometry
