/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopDegree.TopDegreeTraceDefs
import all WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasicDefs

/-! # The local Cartier product and its Kummer sign

Source: sk-cor-trace, complement (ii), proof steps 9--10.
(blueprint: lem-pd-point-product-sign).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
open PurityTransport
variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- The positive Cartier equation in one specified Cartesian coordinate chart.
The two source identifications are fixed by the quotient units, and the target
identification is the root-normalized pullback. Source: sk-cor-trace, complement (ii)
(blueprint: lem-pd-point-product-sign). -/
def PositivePointProduct {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (C : TraceCartierFamily.{u} ell) (x : Spec (.of k) ⟶ X.left)
    [IsClosedImmersion x] (hx : x ≫ X.hom = 𝟙 _) (q : PointCoordinates X d x) : Prop :=
  let s := Spec (.of k)
  let A := iteratedAffineLine s d
  let := residueInverse ell hEll X
  let := residueInverse ell hEll (Over.mk (iteratedAffineLineProj s d))
  let := residueInverse ell hEll q.U
  ∃ (hT : IsUnit (ell : Γ(A, ⊤)))
    (α : (actualPull (c.obj.{u} ell) q.v).obj
      ((actualPush (c.obj.{u} ell) x).obj (U ell c s)) ≅
        (actualPush (c.obj.{u} ell) q.z).obj (U ell c s))
    (β : (actualPull (c.obj.{u} ell) q.t).obj
      (traceProductSource ell c s d (List.finRange d)) ≅
        (actualPush (c.obj.{u} ell) q.z).obj (U ell c s)),
    (tracePullUnit ell c q.v).inv ≫
        (actualPull (c.obj.{u} ell) q.v).map (traceSupportedUnit ell c x) ≫ α.hom =
      traceSupportedUnit ell c q.z ∧
    (tracePullUnit ell c q.t).inv ≫
        (actualPull (c.obj.{u} ell) q.t).map
          (traceProductUnit ell c s d (List.finRange d)) ≫ β.hom =
      traceSupportedUnit ell c q.z ∧
    (actualPull (c.obj.{u} ell) q.v).map (pointMap ell c hEll X d x hx) ≫
        (LinePullCoordinates.derived ell (CurrentTraceCup.linePull ell c q.v) d).hom =
      α.hom ≫ β.inv ≫ (actualPull (c.obj.{u} ell) q.t).map
        (coordinateProduct ell c C false s d hT) ≫
          (LinePullCoordinates.derived ell (CurrentTraceCup.linePull ell c q.t) d).hom

end AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
