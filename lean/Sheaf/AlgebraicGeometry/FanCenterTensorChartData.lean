/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogFanChartBlowup
public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison

/-!
# Data for inverse-image centers and their tensor-chart comparisons

The declarations formerly in `FanCenterLocalBlowupCharts` are retained verbatim,
with their source annotations attached to the data node. This separates the input
and comparison definitions from the theorem so its proof steps can import them.
Source: ILO VIII 3.3.7--3.3.13 (blueprint: def-trf-fan-center-tensor-chart-data).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The affine input in the local clause: a chart lifting the prescribed fan map and
finite nonempty generators of its fan ideal. Generation of the log ideal is deliberately
not part of this input. Multiplication denotes addition in the source.
Source: ILO VIII 3.3.7, 3.3.12--3.3.13
(blueprint: def-trf-fan-center-tensor-chart-data). -/
structure LogFanChart.AffineCenterInput {V : FineSaturatedLogScheme.{u}}
    {F : FineFan.Fan.{u}} (c : LogFanChart V F) (J : FineFan.IdealFamily F) where
  U : V.scheme.Opens
  A : Type u
  ring : CommRing A
  affine : U.toScheme ≅ Spec (.of A)
  P : Type u
  monoid : CommMonoid P
  fs : @IsFineSaturatedMonoid P monoid
  sharp : @FineFan.IsSharp P monoid
  chart : P →* V.logStructure.monoidSheaf.obj.obj (op ((logOpenEtale V.scheme).obj U))
  isChart : V.logStructure.IsChart ((logOpenEtale V.scheme).obj U) chart
  fanChart : FineFan.AffineOpen F.space P
  map : V.logStructure.sharpSpace.restrict U.isOpenEmbedding ⟶ FineFan.affine P
  overFan : map ≫ fanChart.inclusion =
    V.logStructure.sharpSpace.ofRestrict U.isOpenEmbedding ≫ c.map
  sharpens : ∀ (x : U) (p : P),
    FineFan.stalkMap map x (FineFan.affineGerm (map.hom.base x) p) =
      FineFan.stalkMap (V.logStructure.sharpSpace.ofRestrict U.isOpenEmbedding) x
        (FineFan.germ V.logStructure.sharpSpace.presheaf U x.val x.property
          (V.logStructure.sharpSection U (chart p)))
  generators : Finset P
  nonempty : generators.Nonempty
  generates : FineFan.GeneratedOnChart J fanChart generators

attribute [instance] LogFanChart.AffineCenterInput.ring LogFanChart.AffineCenterInput.monoid

/-- Forgetting the single generation proof produces the exact affine ideal chart once
that proof has been supplied. No ideal-generation assertion is assumed in the input.
Source: ILO VIII 3.3.7 (blueprint: def-trf-fan-center-tensor-chart-data). -/
noncomputable def LogFanChart.AffineCenterInput.idealChart {V : FineSaturatedLogScheme.{u}}
    {F : FineFan.Fan.{u}} {c : LogFanChart V F} {J : FineFan.IdealFamily F}
    (D : c.AffineCenterInput J)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ V.scheme)
      (w : (Scheme.pointSmallEtale t).fiber.obj ((logOpenEtale V.scheme).obj D.U)),
      V.logStructure.idealStalk (c.pullbackIdeal J) t =
        {m | ∃ p ∈ D.generators, ∃ n : V.logStructure.toEtalePrelogStructure.stalk t,
          V.logStructure.toEtalePrelogStructure.germ t
            ((logOpenEtale V.scheme).obj D.U) w (D.chart p) * n = m}) :
    LogIdealAffineChart V (c.pullbackIdeal J) where
  W := (logOpenEtale V.scheme).obj D.U
  A := D.A
  ring := D.ring
  affine := D.affine
  P := D.P
  monoid := D.monoid
  fs := D.fs
  chart := D.chart
  isChart := D.isChart
  generators := D.generators
  nonempty := D.nonempty
  generates := h

/-- An open of the scheme defines an open immersion in the small étale site.
Source: ILO VIII 3.3.2 (blueprint: def-trf-fan-center-tensor-chart-data). -/
noncomputable instance logOpenEtale_isOpenImmersion (X : Scheme.{u}) (U : X.Opens) :
    IsOpenImmersion ((logOpenEtale X).obj U).hom :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- The unit face of a chart at a scheme point is the inverse image of the units of
its local ring. Source: ILO VIII 3.3.12 (blueprint: def-trf-fan-center-tensor-chart-data). -/
noncomputable def logChartUnitFace {Z : Scheme.{u}} {P : Type u} [CommMonoid P]
    (α : P →* Γ(Z, ⊤)) (w : Z) : Submonoid P :=
  (IsUnit.submonoid (Z.presheaf.stalk w)).comap
    ((Z.presheaf.germ ⊤ w (by trivial)).hom.toMonoidHom.comp α)

/-- The sharp space restricted to an actual open tensor chart, with its spectrum as
underlying space. Source: ILO VIII 3.3.12
(blueprint: def-trf-fan-center-tensor-chart-data). -/
noncomputable def LogIdealTensorCover.sharpChart
    {V : FineSaturatedLogScheme.{u}} {I : V.logStructure.IdealFamily}
    {D : LogIdealAffineChart V I} {V' : FineSaturatedLogScheme.{u}}
    {b : EtaleLogHom V' V}
    (C : LogIdealTensorCover D b.toLogMap
      (fun a ↦ logIdealSaturatedChartMonoid D.generators a.val)
      (fun a ↦ logIdealSaturatedChartInclusion D.generators a.val))
    (hW : IsOpenImmersion D.W.hom) (a : {a : D.P // a ∈ D.generators}) :
    SheafedSpace CommMonCat.{u} :=
  letI := hW
  letI := C.openImmersion a
  V'.logStructure.sharpSpace.restrict
    (C.toPullback a ≫ pullback.fst b.base D.W.hom).isOpenEmbedding

/-- The canonical inclusion of the restricted sharp space of a tensor chart.
Source: ILO VIII 3.3.12 (blueprint: def-trf-fan-center-tensor-chart-data). -/
noncomputable def LogIdealTensorCover.sharpChartInclusion
    {V : FineSaturatedLogScheme.{u}} {I : V.logStructure.IdealFamily}
    {D : LogIdealAffineChart V I} {V' : FineSaturatedLogScheme.{u}}
    {b : EtaleLogHom V' V}
    (C : LogIdealTensorCover D b.toLogMap
      (fun a ↦ logIdealSaturatedChartMonoid D.generators a.val)
      (fun a ↦ logIdealSaturatedChartInclusion D.generators a.val))
    (hW : IsOpenImmersion D.W.hom) (a : {a : D.P // a ∈ D.generators}) :
    C.sharpChart hW a ⟶ V'.logStructure.sharpSpace :=
  letI := hW
  letI := C.openImmersion a
  V'.logStructure.sharpSpace.ofRestrict
    (C.toPullback a ≫ pullback.fst b.base D.W.hom).isOpenEmbedding

/-- The structural monomials of a tensor chart on its actual affine spectrum.
Source: ILO VIII 3.3.5--3.3.9
(blueprint: def-trf-fan-center-tensor-chart-data). -/
noncomputable def LogIdealTensorCover.ringChart
    {V : FineSaturatedLogScheme.{u}} {I : V.logStructure.IdealFamily}
    {D : LogIdealAffineChart V I} {V' : FineSaturatedLogScheme.{u}}
    {b : EtaleLogHom V' V}
    (_C : LogIdealTensorCover D b.toLogMap
      (fun a ↦ logIdealSaturatedChartMonoid D.generators a.val)
      (fun a ↦ logIdealSaturatedChartInclusion D.generators a.val))
    (a : {a : D.P // a ∈ D.generators}) :
    logIdealSaturatedChartMonoid D.generators a.val →*
      Γ(Spec (.of (logIdealTensorRing D.A D.alpha
        (logIdealSaturatedChartInclusion D.generators a.val))), ⊤) :=
  (Scheme.ΓSpecIso (.of (logIdealTensorRing D.A D.alpha
    (logIdealSaturatedChartInclusion D.generators a.val)))).inv.hom.toMonoidHom.comp
      (logIdealTensorMonomial D.A D.alpha
        (logIdealSaturatedChartInclusion D.generators a.val))

/-- Canonical characteristic comparison on an open tensor chart. Its normalization on
all ambient Zariski log sections fixes the geometric comparison, rather than allowing
an arbitrary abstract isomorphism. Source: ILO VIII 3.3.12--3.3.13
(blueprint: def-trf-fan-center-tensor-chart-data). -/
def LogIdealTensorCover.IsGeometricComparison
    {V : FineSaturatedLogScheme.{u}} {I : V.logStructure.IdealFamily}
    {D : LogIdealAffineChart V I} {V' : FineSaturatedLogScheme.{u}}
    {b : EtaleLogHom V' V}
    (C : LogIdealTensorCover D b.toLogMap
      (fun a ↦ logIdealSaturatedChartMonoid D.generators a.val)
      (fun a ↦ logIdealSaturatedChartInclusion D.generators a.val))
    (hW : IsOpenImmersion D.W.hom) (a : {a : D.P // a ∈ D.generators})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of (logIdealTensorRing D.A D.alpha
      (logIdealSaturatedChartInclusion D.generators a.val))))
    (e : FineFan.stalk (C.sharpChart hW a).presheaf (t default) ≃*
      V'.logStructure.characteristic
        (t ≫ C.toPullback a ≫ pullback.fst b.base D.W.hom)) : Prop :=
  ∀ (U : V'.scheme.Opens)
    (w : (Scheme.pointSmallEtale
      (t ≫ C.toPullback a ≫ pullback.fst b.base D.W.hom)).fiber.obj
        ((logOpenEtale V'.scheme).obj U))
    (hx : (C.toPullback a ≫ pullback.fst b.base D.W.hom) (t default) ∈ U)
    (s : V'.logStructure.monoidSheaf.obj.obj (op ((logOpenEtale V'.scheme).obj U))),
    e (FineFan.stalkMap (C.sharpChartInclusion hW a) (t default)
      (FineFan.germ V'.logStructure.sharpSpace.presheaf U
        ((C.toPullback a ≫ pullback.fst b.base D.W.hom) (t default)) hx
          (V'.logStructure.sharpSection U s))) =
      Associates.mk (V'.logStructure.toEtalePrelogStructure.germ
        (t ≫ C.toPullback a ≫ pullback.fst b.base D.W.hom)
        ((logOpenEtale V'.scheme).obj U) w s)

end AlgebraicGeometry
