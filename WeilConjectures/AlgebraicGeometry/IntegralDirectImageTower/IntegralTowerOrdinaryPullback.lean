/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerPullbackNormalizations
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompactificationScalarSquares
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearNaturalIsoAssembly
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Normalized IntegralTowerOrdinaryPullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

private theorem geometric_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules l E Y) (N : spIntegralSectionModules l E X)
    (a b : (spIntegralModuleEquivalence l E X).functor.obj
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) ⟶ N)
    (h : ∀ (V : Y.ProEt)
      (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)),
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op V) x) =
      b.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op V) x)) : a = b := by
  classical
  let F := (spIntegralModuleEquivalence l E X).functor
  let N' := F.objPreimage N
  let e := F.objObjPreimageIso N
  let a' := F.preimage (a ≫ e.inv)
  let b' := F.preimage (b ≫ e.inv)
  have ha : F.map a' = a ≫ e.inv := F.map_preimage _
  have hb : F.map b' = b ≫ e.inv := F.map_preimage _
  have he : a' = b' := by
    apply ((CondensedRing.upperStarLowerStarAdjunction
      (spIntegralCondensed l E) f).homEquiv M N').injective
    apply Mod.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    ext x
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have haV := congrArg (fun z ↦ z.val.app
      (op ((Scheme.proEtaleBaseChange f).obj V.unop))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        M).hom.hom.app V x)) ha
    have hbV := congrArg (fun z ↦ z.val.app
      (op ((Scheme.proEtaleBaseChange f).obj V.unop))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        M).hom.hom.app V x)) hb
    change a'.hom.hom.app _ _ = b'.hom.hom.app _ _
    exact haV.trans ((congrArg (e.inv.val.app
      (op ((Scheme.proEtaleBaseChange f).obj V.unop))) (h V.unop x)).trans hbV.symm)
  apply (cancel_mono e.inv).mp
  exact ha.symm.trans ((congrArg F.map he).trans hb)

private theorem scalar_geometric_hom_ext (s : Presentation l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules l E Y) (n : ℕ)
    (N : Scheme.proEtaleRingModules X (SpTowerShriek.B l E X n))
    (a b : (ordinaryLevel l E s X n).obj
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) ⟶ N)
    (h : ∀ (V : Y.ProEt)
      (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)),
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul ((s.towers X).scalar
          (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
          ((spIntegralModuleEquivalence l E X).functor.obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x)) =
      b.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul ((s.towers X).scalar
          (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
          ((spIntegralModuleEquivalence l E X).functor.obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x))) : a = b := by
  let A := (s.towers X).scalar
    (spIntegralReductionScalar l E X (s.reduction X).coefficient n)
  apply (A.ordinaryAdj.homEquiv _ N).injective
  apply geometric_hom_ext l E f M
  intro V x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change a.val.app _ ((A.ordinaryAdj.unit.app _).val.app _ _) =
    b.val.app _ ((A.ordinaryAdj.unit.app _).val.app _ _)
  rw [A.unit_normalized]
  exact h V x

private def generator (s : Presentation l E) (e : Evaluation l E s) (T : Scheme.{u})
    (M : Modules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj M).val.obj U) :
    ((SpTowerShriek.ev l E T n).obj ((ordinaryReduction l E s T).obj M)).val.obj U :=
  (((ordinaryReductionEvaluation l E s e T n).inv.app M).val.app U)
    (systemModelTmul ((s.towers T).scalar
      (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
      ((spIntegralModuleEquivalence l E T).functor.obj M) U 1 x)

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
