/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.FiberRank
import WeilConjectures.TraceFormula.PointFiberFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift

/-! # Exact rank of point sections of condensed fibres -/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Endofunctor
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

private theorem point_sections_finrank_free (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) (r : ℕ) :
    Module.finrank (ULift.{u + 1} (PadicAlgCl l))
      ((CondensedRing.pointSections l D.k).obj
        (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l)
          (Spec (.of D.k))) r)) = r := by
  haveI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  haveI : IsSepClosed D.k := IsSepClosed.of_isAlgClosed D.k
  let F := CondensedRing.pointSections l D.k
  let R := condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of D.k))
  let e : F.obj (Mod.finiteFree R r) ≅
      ModuleCat.of _ (Fin r → F.obj (Mod.regular R)) :=
    F.mapBiproduct (fun _ : Fin r ↦ Mod.regular R) ≪≫
      ModuleCat.biproductIsoPi _
  let u := (CondensedRing.pointSectionsUnitIso l D.k).symm
  let u' : F.obj (Mod.regular R) ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
      ULift.{u + 1} (PadicAlgCl l) := by
    exact u.toLinearEquiv
  let p : (Fin r → F.obj (Mod.regular R)) ≃ₗ[
      ULift.{u + 1} (PadicAlgCl l)] (Fin r → ULift.{u + 1} (PadicAlgCl l)) :=
    LinearEquiv.piCongrRight (fun _ : Fin r ↦ u')
  rw [e.toLinearEquiv.finrank_eq, p.finrank_eq]
  exact Module.finrank_fin_fun _

theorem condensed_fibres_point_rank
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    fibreRankAssertions l (D.geometricFiber Y₀).left
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedRing.pointSections l D.k) := by
  haveI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  haveI : IsSepClosed D.k := IsSepClosed.of_isAlgClosed D.k
  clear hl hz
  intro M r hM
  obtain ⟨U, hU⟩ := hM
  obtain ⟨i, g, hg⟩ := U.exists_comp_eq_of_isSepClosed_of_proetale z
  obtain ⟨e⟩ := hU i
  let P := CondensedRing.pointSections l D.k
  let A := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (U.f i)
  let B := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g
  let C := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
  let ec : B.obj (A.obj M) ≅ C.obj M :=
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) g (U.f i)).symm.app M ≪≫
      (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) hg).app M
  let eb : B.obj (Mod.finiteFree
      (condensedRingObj (Profinite.padicAlgClRingObj l) (U.X i)) r) ≅
      Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Spec (.of D.k))) r :=
    CondensedRing.upperStarFiniteFreeIso (Profinite.padicAlgClRingObj l) g r
  let ep : P.obj (C.obj M) ≅ P.obj (B.obj (A.obj M)) :=
    P.mapIso ec.symm
  let em : P.obj (B.obj (A.obj M)) ≅ P.obj (B.obj
      (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) (U.X i)) r)) :=
    P.mapIso (B.mapIso e)
  let ef : P.obj (B.obj (Mod.finiteFree
      (condensedRingObj (Profinite.padicAlgClRingObj l) (U.X i)) r)) ≅
      P.obj (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Spec (.of D.k))) r) :=
    P.mapIso eb
  calc
    Module.finrank _ (P.obj (C.obj M)) = Module.finrank _ (P.obj (B.obj (A.obj M))) :=
      ep.toLinearEquiv.finrank_eq
    _ = Module.finrank _ (P.obj (B.obj
        (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) (U.X i)) r))) :=
      em.toLinearEquiv.finrank_eq
    _ = Module.finrank _ (P.obj (Mod.finiteFree
        (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of D.k))) r)) :=
      ef.toLinearEquiv.finrank_eq
    _ = r := point_sections_finrank_free l D r

end WeilConjectures
