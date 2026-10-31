/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.VerdierExchangeData

/-! # Site exchange comparisons under the smooth orientation

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
thm-pod-global-verdier-duality.proof.md, second paragraph
(blueprint: def-pod-smooth-orientation-transport-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] CategoryTheory.Functor.mapIso CategoryTheory.Iso.trans

/-- Forward and inverse coefficient squares for the same specified purity map.
The inputs are the actual source and exceptional comparisons; this abbreviation
asserts both arrow equations without choosing any replacement maps.
Source: latest blueprint, global Verdier duality proof, purity comparison calculation
(blueprint: def-pod-smooth-orientation-transport-square). -/
@[irreducible] def smoothOrientationPuritySquare
    {C : Type (u + 2)} [Category.{u + 2} C]
    {D : Type (u + 2)} [Category.{u + 2} D]
    (Q : C ⥤ D) {A B : C} {A' B' : D}
    (γ : A ≅ B) (γ' : A' ≅ B')
    (h : Q.obj A ≅ A') (z : Q.obj B ≅ B') : Prop :=
  Q.map γ.hom ≫ z.hom = h.hom ≫ γ'.hom ∧
    Q.map γ.inv ≫ h.hom = z.hom ≫ γ'.inv

/-- The smooth-orientation transport equation on the recorded closed coefficient
categories. `theta` is literally the internal-Hom action of the inverse purity map;
`cH` is the evaluation transpose using the source tensor/twist/shift comparison.
Source: latest blueprint, global Verdier duality proof, final transport calculation
(blueprint: def-pod-smooth-orientation-transport-square). -/
@[irreducible] def smoothOrientationTransportSquare
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    {X Y Z : Scheme.{u}} {s t : ConstructibleExceptionalCoefficients.Stage.{u} l}
    {Fs : ConstructibleExceptionalCoefficients.Operation l Ω X Y s}
    {As : ConstructibleExceptionalCoefficients.Operation l Ω Y Z s}
    {Bs : ConstructibleExceptionalCoefficients.Operation l Ω X Z s}
    {us : ConstructibleExceptionalCoefficients.C.{u, u} l Ω Z s}
    {Ft : ConstructibleExceptionalCoefficients.Operation l Ω X Y t}
    {At : ConstructibleExceptionalCoefficients.Operation l Ω Y Z t}
    {Bt : ConstructibleExceptionalCoefficients.Operation l Ω X Z t}
    {ut : ConstructibleExceptionalCoefficients.C.{u, u} l Ω Z t}
    (ds : VerdierExchange.StageData l Ω s Fs As Bs us)
    (dt : VerdierExchange.StageData l Ω t Ft At Bt ut)
    {TX : ConstructibleExceptionalCoefficients.C.{u, u} l Ω X s ⥤
      ConstructibleExceptionalCoefficients.C.{u, u} l Ω X t}
    {TY : ConstructibleExceptionalCoefficients.C.{u, u} l Ω Y s ⥤
      ConstructibleExceptionalCoefficients.C.{u, u} l Ω Y t}
    {TZ : ConstructibleExceptionalCoefficients.C.{u, u} l Ω Z s ⥤
      ConstructibleExceptionalCoefficients.C.{u, u} l Ω Z t}
    (b : VerdierExchange.StageScalar l Ω ds dt TX TY TZ)
    (Hs : ConstructibleExceptionalCoefficients.C.{u, u} l Ω X s)
    (Ht : ConstructibleExceptionalCoefficients.C.{u, u} l Ω X t)
    (γs : Hs ≅ Bs.G.obj us) (γt : Ht ≅ Bt.G.obj ut)
    (hQ : TX.obj Hs ⟶ Ht)
    (K : ConstructibleExceptionalCoefficients.C.{u, u} l Ω X s) : Prop :=
  let Ps := ds.homX.obj (op K, Hs)
  let Pt := dt.homX.obj (op (TX.obj K), Ht)
  let θs : (ds.dualX l Ω).obj (op K) ⟶ Ps :=
    ds.homX.map (Prod.mkHom (𝟙 (op K)) γs.inv)
  let θt : (dt.dualX l Ω).obj (op (TX.obj K)) ⟶ Pt :=
    dt.homX.map (Prod.mkHom (𝟙 (op (TX.obj K))) γt.inv)
  let cH : TX.obj Ps ⟶ Pt :=
    dt.closedX.transpose _ (TX.obj K) Ht
      (b.tensorX.inv.app (Ps, K) ≫
        TX.map (ds.closedX.evaluation K Hs) ≫ hQ)
  let RQH : TY.obj (ds.star.obj Ps) ⟶ dt.star.obj Pt :=
    VerdierExchange.StageScalar.star l Ω b Ps ≫ dt.star.map cH
  let RQ := VerdierExchange.StageScalar.star l Ω b
      ((ds.dualX l Ω).obj (op K)) ≫
    dt.star.map (VerdierExchange.StageScalar.dualX l Ω b K)
  let uQ := (ConstructibleExceptionalCoefficients.FieldComparison.q l Ω b.exceptional).app K
  let δQC := VerdierExchange.StageScalar.dualY l Ω b (Fs.F.obj K)
  TX.map θs ≫ cH = VerdierExchange.StageScalar.dualX l Ω b K ≫ θt ∧
  TY.map (ds.star.map θs) ≫ RQH = RQ ≫ dt.star.map θt ∧
  TY.map (ds.epsilon l Ω K ≫ ds.star.map θs) ≫ RQH =
    δQC ≫ (dt.dualY l Ω).map uQ.inv.op ≫
      dt.epsilon l Ω (TX.obj K) ≫ dt.star.map θt

/-- The actual exchange coefficient equation for the recorded exchange components.
The scalar source map is the evaluation-transposed Hom comparison followed by
precomposition with the inverse compact-support comparison. The target map is the
ordinary-direct-image comparison followed by the evaluation-transposed dual map.
Source: latest blueprint, global Verdier duality proof, coefficient exchange equation
(blueprint: def-pod-smooth-orientation-transport-square). -/
@[irreducible] def smoothOrientationExchangeSquare
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    {X Y Z : Scheme.{u}} {s t : ConstructibleExceptionalCoefficients.Stage.{u} l}
    {Fs : ConstructibleExceptionalCoefficients.Operation l Ω X Y s}
    {As : ConstructibleExceptionalCoefficients.Operation l Ω Y Z s}
    {Bs : ConstructibleExceptionalCoefficients.Operation l Ω X Z s}
    {us : ConstructibleExceptionalCoefficients.C.{u, u} l Ω Z s}
    {Ft : ConstructibleExceptionalCoefficients.Operation l Ω X Y t}
    {At : ConstructibleExceptionalCoefficients.Operation l Ω Y Z t}
    {Bt : ConstructibleExceptionalCoefficients.Operation l Ω X Z t}
    {ut : ConstructibleExceptionalCoefficients.C.{u, u} l Ω Z t}
    (ds : VerdierExchange.StageData l Ω s Fs As Bs us)
    (dt : VerdierExchange.StageData l Ω t Ft At Bt ut)
    {TX : ConstructibleExceptionalCoefficients.C.{u, u} l Ω X s ⥤
      ConstructibleExceptionalCoefficients.C.{u, u} l Ω X t}
    {TY : ConstructibleExceptionalCoefficients.C.{u, u} l Ω Y s ⥤
      ConstructibleExceptionalCoefficients.C.{u, u} l Ω Y t}
    {TZ : ConstructibleExceptionalCoefficients.C.{u, u} l Ω Z s ⥤
      ConstructibleExceptionalCoefficients.C.{u, u} l Ω Z t}
    (b : VerdierExchange.StageScalar l Ω ds dt TX TY TZ)
    (es : VerdierExchange.StageConclusion l Ω ds)
    (et : VerdierExchange.StageConclusion l Ω dt)
    (K : ConstructibleExceptionalCoefficients.C.{u, u} l Ω X s) : Prop :=
  let e := (es.epsilon.app (op K)).hom
  let e' := (et.epsilon.app (op (TX.obj K))).hom
  let uQ := (ConstructibleExceptionalCoefficients.FieldComparison.q l Ω b.exceptional).app K
  let δQC := VerdierExchange.StageScalar.dualY l Ω b (Fs.F.obj K)
  let RQ := VerdierExchange.StageScalar.star l Ω b
      ((ds.dualX l Ω).obj (op K)) ≫
    dt.star.map (VerdierExchange.StageScalar.dualX l Ω b K)
  TY.map e ≫ RQ = δQC ≫ (dt.dualY l Ω).map uQ.inv.op ≫ e'

end WeilConjectures
