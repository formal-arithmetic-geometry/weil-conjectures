/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundaryRestrictionUnderlying
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalFiniteConeChernClass
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryEndpointMaps

/-! Target endpoint transport for the finite Chern coordinate. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

private theorem scalarUnitSection_local (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (c : Chern l (ULift.{u} (Padic l)) T)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x : c.rootModule.val.obj (op (n, U.unop))) :
    (c.scalar.ordinaryAdjunction.unit.app c.rootModule).val.app
        (op (n, U.unop)) x =
      SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
        (coefficientSystemMap l (ULift.{u} (Padic l)) T)
        c.scalar c.rootModule (op (n, U.unop)) x := by
  change _ = (eqToHom (c.scalar.model.obj_eq c.rootModule).symm).val.app
    (op (n, U.unop))
    (SemilinearSections.extensionUnit
      (coefficientSystemMap l (ULift.{u} (Padic l)) T) c.rootModule
      (op (n, U.unop)) x)
  rw [← c.scalar.unit_section c.rootModule (op (n, U.unop)) x]
  exact (congrArg
    (fun a ↦ a.val.app (op (n, U.unop))
      ((c.scalar.ordinaryAdjunction.unit.app c.rootModule).val.app
        (op (n, U.unop)) x))
    (eqToIso (c.scalar.model.obj_eq c.rootModule)).hom_inv_id).symm

/-- Target endpoint transport.  The finite root map, the inverse line
comparison, and the coefficient lineForget map compose to the Cartier root
map.  The proof expands `finiteBoundary_rootMap`, uses the ordinary scalar unit
and `line_tensor`, and cancels the evaluation and restriction isomorphisms.
(blueprint: lem-diagonal-local-finite-target-endpoint-transport) -/
theorem finiteBoundary_target_endpoint
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (A : Type (u + 1))
    [CommRing A] (n : ℕ) (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) :
    let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
    let e := finiteBoundaryRestrictionUnderlying l T r n
    S.map (finiteRootMap l (ULift.{u} (Padic l)) T n) ≫
        S.map ((finiteForget l (ULift.{u} (Padic l)) T n).mapIso
          (lineEvaluation l (ULift.{u} (Padic l)) c n)).inv ≫
        S.map (e.inv.app (lineModule l (ULift.{u} (Padic l)) c)) ≫
        S.map (k.lineForget.hom.app (op n)) ≫
        S.map (cartierProRootMap A (l ^ (n + 1)) hA T
          (pow_pos (Fact.out : l.Prime).pos _) hN) =
      S.map (cartierProRootMap A (l ^ (n + 1)) hA T
      (pow_pos (Fact.out : l.Prime).pos _) hN) := by
  let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
  let e := finiteBoundaryRestrictionUnderlying l T r n
  change S.map (finiteRootMap l (ULift.{u} (Padic l)) T n) ≫
      S.map ((finiteForget l (ULift.{u} (Padic l)) T n).map
        (lineEvaluation l (ULift.{u} (Padic l)) c n).inv) ≫
      S.map (e.inv.app (lineModule l (ULift.{u} (Padic l)) c)) ≫
      S.map (k.lineForget.hom.app (op n)) ≫
      S.map (cartierProRootMap A (l ^ (n + 1)) hA T
        (pow_pos (Fact.out : l.Prime).pos _) hN) =
    S.map (cartierProRootMap A (l ^ (n + 1)) hA T
      (pow_pos (Fact.out : l.Prime).pos _) hN)
  have hr := SpTowerClasses.finiteBoundary_rootMap l (ULift.{u} (Padic l)) c n
  have hbase :
      finiteRootMap l (ULift.{u} (Padic l)) T n ≫
          (finiteForget l (ULift.{u} (Padic l)) T n).map
            (lineEvaluation l (ULift.{u} (Padic l)) c n).inv ≫
          (finiteBoundaryRestrictionUnderlying l T r n).inv.app
            (lineModule l (ULift.{u} (Padic l)) c) ≫
          k.lineForget.hom.app (op n) = 𝟙 _ := by
    rw [← hr]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, Category.assoc]
    have hmap := (finiteForget l (ULift.{u} (Padic l)) T n).map_id
      ((SpTowerShriek.ev l (ULift.{u} (Padic l)) T n).obj
        (lineModule l (ULift.{u} (Padic l)) c))
    rw [hmap, Category.id_comp]
    apply Sheaf.hom_ext
    ext U z
    let x' := (c.rootForget.inv.app (op n)).hom.app U z
    let x := (eqToHom (c.reduction.forget.sections c.rootModule n U)) x'
    have hx : HEq x' x :=
      (SpTowerClasses.finiteBoundary_cast_heq
        (c.reduction.forget.sections c.rootModule n U) x').symm
    let η := c.scalar.ordinaryAdjunction.unit.app c.rootModule
    have hf := SpTowerClasses.finiteBoundary_forgetMapSection T _
      c.reduction.forget η n U x x' hx
    have he := SpTowerClasses.finiteScalarForgetIso_section l
      (ULift.{u} (Padic l)) c n (lineModule l (ULift.{u} (Padic l)) c) U _ _ hf
    let v := ((finiteScalarForgetIso l (ULift.{u} (Padic l)) c n).hom.app
      (lineModule l (ULift.{u} (Padic l)) c)).hom.app U
        (((c.reduction.forget.F.map η).app (op n)).hom.app U x')
    let w := (e.inv.app (lineModule l (ULift.{u} (Padic l)) c)).hom.app U v
    have hw : HEq w v := by
      change HEq ((eqToHom (r.underlying (lineModule l (ULift.{u} (Padic l)) c)
        n U).symm) v) v
      exact SpTowerClasses.finiteBoundary_cast_heq _ _
    have hu : η.val.app (op (n, U.unop)) x =
        SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
          (coefficientSystemMap l (ULift.{u} (Padic l)) T)
          c.scalar c.rootModule (op (n, U.unop)) x :=
      scalarUnitSection_local l T c n U x
    have ht := k.line_tensor n U x x' w hx.symm
      (hw.trans ((heq_of_eq he).trans (heq_of_eq hu)))
    have hi := congrArg (fun f ↦ f.hom.app U z)
      (c.rootForget.app (op n)).inv_hom_id
    change (c.rootForget.hom.app (op n)).hom.app U x' = z at hi
    change (k.lineForget.hom.app (op n)).hom.app U w = z
    rw [ht, hi]
  simp only [← Functor.map_comp_assoc]
  rw [hbase]
  rw [← S.map_comp, Category.id_comp]

end AlgebraicGeometry.ProEtale.DiagonalTrace
