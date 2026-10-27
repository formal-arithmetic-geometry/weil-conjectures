/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FanCenterTensorChartData

/-!
# Coherence and affine generators of an inverse-image fan center

Source: ILO VIII 3.3.7, 3.3.12--3.3.13(i).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Inverse-image fan ideals are coherent, with the prescribed generators on every
lifted affine chart. This is only the ideal calculation, before constructing a blowup.

Source: ILO VIII 3.1.18, 3.1.25(i), 3.3.7, 3.3.12--3.3.13(i)
(blueprint: lem-trf-fan-center-pullback-coherence).

Proof: Near each scheme point, use `fan_chart_local_monoid_lift` to lift the
characteristic chart of the fan stalk to the log structure. By
`fineFan_point_localization`, this stalk is the section monoid on the smallest
fan neighborhood. Restrict a finite nonempty set of generators of J to this
neighborhood, and shrink the scheme neighborhood to an affine open. In a
geometric stalk, membership in the characteristic ideal says that a class is
[h(p)] times another class, for p among the generators. Lift the other class
to a log element. Equality of classes means equality up to a log unit; absorb
that unit into the second factor. Conversely, every such product lies above
the characteristic ideal. This argument applies to every supplied affine chart,
using its `sharpens` equation, and proves the displayed stalk equality. The
pointwise definition of `pullbackIdeal` is stable under multiplication and
restriction; membership detected on all geometric stalks is its defining local
condition. Thus it is an ideal subsheaf. The preceding neighborhoods give the
finite nonempty chart witnesses for coherence. -/
theorem fan_center_pullback_coherence
    (V : FineSaturatedLogScheme.{u}) (F : FineFan.Fan.{u})
    (c : LogFanChart V F) (J : FineFan.IdealFamily F)
    (hJ : FineFan.IsNonemptyCoherentIdeal J) :
    V.logStructure.IsNonemptyCoherentIdeal (c.pullbackIdeal J) ∧
    ∀ D : c.AffineCenterInput J,
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ V.scheme)
        (w : (Scheme.pointSmallEtale t).fiber.obj ((logOpenEtale V.scheme).obj D.U)),
        V.logStructure.idealStalk (c.pullbackIdeal J) t =
          {m | ∃ p ∈ D.generators, ∃ n : V.logStructure.toEtalePrelogStructure.stalk t,
            V.logStructure.toEtalePrelogStructure.germ t
              ((logOpenEtale V.scheme).obj D.U) w (D.chart p) * n = m} := by sorry

end AlgebraicGeometry
