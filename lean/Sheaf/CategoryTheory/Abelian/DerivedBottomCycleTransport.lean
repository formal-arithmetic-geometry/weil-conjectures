/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Sheaf.CategoryTheory.Abelian.DerivedSingleShiftNormalization
import Sheaf.CategoryTheory.Abelian.DerivedBottomComparison

/-! # Canonical-cycle transport to the double truncation

Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-bottom-cycle-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
  [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D]
  (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S]

/-- The part of the bottom comparison before the single-object normalization.
All maps are taken from its explicit double-truncation construction.
Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-bottom-cycle-transport). -/
noncomputable def rightDerivedBottomToSingleIso (n : ℤ) :
    DerivedCategory.TStructure.t.truncGE n ⋙ S.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor D n ≅
    DerivedCategory.TStructure.t.truncGE n ⋙ DerivedCategory.homologyFunctor C n ⋙
      DerivedCategory.Plus.singleFunctor C n ⋙ S.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor D n := by
  let t := DerivedCategory.TStructure.t (C := C)
  let tp := DerivedCategory.Plus.TStructure.t (C := C)
  let L := t.plus.lift (t.truncGE n) (fun K ↦ ⟨n, inferInstance⟩)
  let H := DerivedCategory.Plus.homologyFunctor D n
  let R := S.rightDerivedFunctorPlus
  let α := Functor.whiskerLeft L
    (Functor.whiskerRight (Functor.whiskerRight (tp.truncLTι (n + 1)) R) H)
  have (K : DerivedCategory C) : IsIso (α.app K) := by
    let M := L.obj K
    let T := (R ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      ((tp.triangleLTGE (n + 1)).obj M)
    have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
      (R ⋙ DerivedCategory.Plus.ι).map_distinguished _
        (tp.triangleLTGE_distinguished (n + 1) M)
    have hz (j : ℤ) (hj : j < n + 1) :
        Limits.IsZero ((DerivedCategory.homologyFunctor D j).obj T.obj₃) := by
      exact S.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        ((tp.truncGE (n + 1)).obj M) (n + 1) hj
    exact DerivedCategory.isIso_homologyMap_mor₁ T hT (n - 1) n (by omega)
      (hz (n - 1) (by omega)) (hz n (by omega))
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let β := Functor.whiskerLeft L
    (Functor.whiskerLeft (tp.truncLT (n + 1))
      (Functor.whiskerRight (Functor.whiskerRight (tp.truncGEπ n) R) H))
  have (K : DerivedCategory C) : IsIso (β.app K) := by
    have : tp.IsGE (L.obj K) n := by
      apply (DerivedCategory.Plus.isGE_ι_obj_iff (L.obj K) n).mp
      change t.IsGE ((t.truncGE n).obj K) n
      infer_instance
    have : IsIso ((tp.truncGEπ n).app ((tp.truncLT (n + 1)).obj (L.obj K))) :=
      inferInstance
    change IsIso (H.map (R.map _))
    infer_instance
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let eT := DerivedCategory.Plus.eTruncLTCompETruncGEIso (C := C) n
  let Hn := DerivedCategory.Plus.homologyFunctor C n
  let e := (asIso α).symm ≪≫ asIso β ≪≫
    Functor.isoWhiskerLeft L (Functor.isoWhiskerRight eT (R ⋙ H))
  let HA := DerivedCategory.homologyFunctor D n
  let eP := Functor.isoWhiskerLeft L
    (Functor.isoWhiskerRight S.rightDerivedFunctorPlusCompatibility.symm HA)
  exact eP ≪≫ e

/-- Transport of canonical cycles to the actual unit on the single homology object.

Source: Stacks Project, Tag 05TC (2), with the unit of Tag 05TD (3).
(blueprint: new-lem-pc-derived-bottom-cycle-transport).

Proof: Replace the lower derived truncation by the localization of smart
truncation of K. Its bottom term is K.X n modulo the incoming boundaries,
and its cycles identify with H^n(K). The canonical cycle map followed by
this identification is the homology quotient of K. The map from the upper
smart truncation to the lower one induces an invertible H^n after deriving
S; naturality of the actual derived unit lets its inverse cancel the
inclusion. The projection of that upper truncation to the double truncation
is invertible and identifies the remaining map with the unit on the single
object. The homology formula for eTruncLTCompETruncGEIso identifies the
source map with the quotient followed by the lower-truncation homology
map, with no choice of sign. Finally the uniqueness comparison of bounded
below and unbounded derived functors intertwines their actual units.
Apply homology and its localization factor isomorphism to obtain the
stated equation. This calculation does not use the single-object comparison
or its shift normalization; it stops at the actual unit on that object. -/
theorem rightDerivedBottom_cycle_transport (n : ℤ) (K : CochainComplex C ℤ) :
    ((((S.mapHomologicalComplex (.up ℤ)).obj K).sc n).liftCycles
        (S.map (K.sc n).iCycles) (by
          change S.map (K.sc n).iCycles ≫ S.map (K.sc n).g = 0
          rw [← S.map_comp, (K.sc n).iCycles_g, S.map_zero])) ≫
      (((S.mapHomologicalComplex (.up ℤ)).obj K).sc n).homologyπ ≫
          ((DerivedCategory.homologyFunctorFactors D n).app
            ((S.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
          (DerivedCategory.homologyFunctor D n).map
            (S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≫
          (DerivedCategory.homologyFunctor D n).map
            (S.rightDerivedFunctor.map
              ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K))) ≫
          (S.rightDerivedBottomToSingleIso n).hom.app (DerivedCategory.Q.obj K) =
      S.map ((K.sc n).homologyπ ≫
        ((DerivedCategory.homologyFunctorFactors C n).app K).inv ≫
        (DerivedCategory.homologyFunctor C n).map
          ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K))) ≫
      S.rightDerivedPlusSingleUnitHomologyAt n
        ((DerivedCategory.homologyFunctor C n).obj
          ((DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj K))) := by sorry

end CategoryTheory.Functor
