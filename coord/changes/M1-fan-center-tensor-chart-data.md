# AlgebraicGeometry.LogFanChart.AffineCenterInput and tensor-chart data

## Reason

The local proof steps need the existing data definitions without importing the theorem
that combines them. Relocate those declarations into the new module
`Sheaf.AlgebraicGeometry.FanCenterTensorChartData`, publicly imported by the original
module. Their names, signatures, attributes and bodies remain identical; only the
blueprint tags identify the new data node. The original legacy file becomes a module
file with an exposed public section. No mathematical definition or target changes.
There are no direct Lean importers of the original module. Its DAG parents are retained.

## Old

In `lean/Sheaf/AlgebraicGeometry/FanCenterLocalBlowupCharts.lean`:

```lean
/-- The affine input in the local clause: a chart lifting the prescribed fan map and
finite nonempty generators of its fan ideal. Generation of the log ideal is deliberately
not part of this input. Multiplication denotes addition in the source.
Source: ILO VIII 3.3.7, 3.3.12--3.3.13
(blueprint: lem-trf-fan-center-local-blowup-charts). -/
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
Source: ILO VIII 3.3.7 (blueprint: lem-trf-fan-center-local-blowup-charts). -/
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
Source: ILO VIII 3.3.2 (blueprint: lem-trf-fan-center-local-blowup-charts). -/
noncomputable instance logOpenEtale_isOpenImmersion (X : Scheme.{u}) (U : X.Opens) :
    IsOpenImmersion ((logOpenEtale X).obj U).hom :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- The unit face of a chart at a scheme point is the inverse image of the units of
its local ring. Source: ILO VIII 3.3.12 (blueprint: lem-trf-fan-center-local-blowup-charts). -/
noncomputable def logChartUnitFace {Z : Scheme.{u}} {P : Type u} [CommMonoid P]
    (α : P →* Γ(Z, ⊤)) (w : Z) : Submonoid P :=
  (IsUnit.submonoid (Z.presheaf.stalk w)).comap
    ((Z.presheaf.germ ⊤ w (by trivial)).hom.toMonoidHom.comp α)

/-- The sharp space restricted to an actual open tensor chart, with its spectrum as
underlying space. Source: ILO VIII 3.3.12
(blueprint: lem-trf-fan-center-local-blowup-charts). -/
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
Source: ILO VIII 3.3.12 (blueprint: lem-trf-fan-center-local-blowup-charts). -/
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
(blueprint: lem-trf-fan-center-local-blowup-charts). -/
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
(blueprint: lem-trf-fan-center-local-blowup-charts). -/
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

```

## New

In `lean/Sheaf/AlgebraicGeometry/FanCenterTensorChartData.lean`:

```lean
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

```

The original module has `public import Sheaf.AlgebraicGeometry.FanCenterTensorChartData`
and retains the verbatim signature of `fan_center_local_blowup_charts`.
No other existing module is changed. The proof-only imports of the new split modules
remain private; there are no new elaboration attributes or file-level transparency overrides.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FanCenterLocalBlowupCharts | M1 | Same data names re-exported; theorem signature unchanged; proof now assembles the steps. |
| Sheaf.AlgebraicGeometry.FanCenterPullbackCoherence | M1 (new) | Uses the relocated affine input. |
| Sheaf.AlgebraicGeometry.FanCenterBlowupZariski | M1 (new) | Uses the same log/fan definitions. |
| Sheaf.AlgebraicGeometry.FanCenterTensorChartComparison | M1 (new) | Uses the relocated tensor-chart comparison definitions. |

`tools/downstream.py Sheaf.AlgebraicGeometry.FanCenterLocalBlowupCharts --uses
AlgebraicGeometry.LogFanChart.AffineCenterInput` reports zero downstream modules and only
the item itself as a declaration user. The direct-import search also finds zero importers,
so there are no existing consumer copies to compile or adapt. All five delivery modules
are compiled together against the new definitions.

## Status

landed 20261026T091953-L-3390847 2026-10-26 (merge of deliver/M1/Sheaf.AlgebraicGeometry.FanCenterLocalBlowupCharts)
