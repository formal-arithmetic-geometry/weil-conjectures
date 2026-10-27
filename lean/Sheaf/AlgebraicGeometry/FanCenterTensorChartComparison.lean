/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FanCenterTensorChartData

/-!
# The normalized fan comparison on one supplied saturated tensor chart

Source: ILO VIII 3.1.19--3.1.25, 3.3.12--3.3.13(i),(iii).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- A single already supplied saturated tensor chart has the normalized
comparison with any supplied saturated fan blowup. This neither proves coherence
nor constructs the log blowup or the cover.

Source: ILO VIII 3.1.19--3.1.25, 3.3.12--3.3.13(i),(iii)
(blueprint: lem-trf-fan-center-tensor-chart-comparison).

Proof: Write R for the saturated fraction monoid of the selected generator a.
The affine construction of the fan blowup gives its open S(R). Its inclusion
K is independent of the initial presentation: on a common localization, both
constructions invert precisely the fractions making a generate the ideal;
these inclusions in P^gp agree on every overlap and their triple cocycle is
the identity. The tensor chart has the associated log structure of the
canonical R monomials, by `C.isChart` and `C.chartAlpha`. Apply
`monoid_chart_characteristic_fan` to this open chart. Transport its sharp
space map to the restriction of the ambient sharp space using the Zariski
association and its canonical comparison on all ambient log-section germs.
This gives f, its locality and its bijective stalk maps. The log morphism b
induces g by quotienting its section maps by units and sheafifying. The
`C.chartMap` equality and `D.sharpens` say that f followed by the fan blowup
and the map induced by b pull every p in P to the same characteristic germ.
Injectivity in `affine_hom_universal` makes these full morphisms equal.
At a geometric point t let H be the elements of R whose monomials map to
units of the local ring. The characteristic-fan theorem identifies the fan
stalk and the log characteristic with Associates(R localized at H). Transfer
these identifications along the open inclusion K to obtain eF and eN.
Their normalization on canonical numerators gives r, s and all four equations
for every q. The same theorem identifies the ordinary restricted sharp
stalk with the geometric characteristic; use this identification for e.
Its normalization on all Zariski log-section germs is the displayed geometric
comparison. Both composites from the fan stalk agree on numerator classes,
which generate its face localization modulo units, so e composed with the
stalk map equals eN composed with eF on every element. -/
theorem fan_center_tensor_chart_comparison
    (V : FineSaturatedLogScheme.{u}) (F : FineFan.Fan.{u})
    (c : LogFanChart V F) (J : FineFan.IdealFamily F)
    (V' : FineSaturatedLogScheme.{u}) (b : EtaleLogHom V' V)
    (hb : IsSaturatedLogBlowup b (c.pullbackIdeal J))
    (hz : V'.logStructure.IsZariski) (D : c.AffineCenterInput J)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ V.scheme)
        (w : (Scheme.pointSmallEtale t).fiber.obj ((logOpenEtale V.scheme).obj D.U)),
        V.logStructure.idealStalk (c.pullbackIdeal J) t =
          {m | ∃ p ∈ D.generators, ∃ n : V.logStructure.toEtalePrelogStructure.stalk t,
            V.logStructure.toEtalePrelogStructure.germ t
              ((logOpenEtale V.scheme).obj D.U) w (D.chart p) * n = m})
    (C : LogIdealTensorCover (D.idealChart h) b.toLogMap
      (fun a ↦ logIdealSaturatedChartMonoid D.generators a.val)
      (fun a ↦ logIdealSaturatedChartInclusion D.generators a.val))
    (F' : FineFan.Fan.{u}) (β : FineFan.Hom F' F)
    (hβ : FineFan.IsSaturatedBlowup β J) (a : {a : D.P // a ∈ D.generators}) :
    ∃ (K : FineFan.AffineOpen F'.space
        (logIdealSaturatedChartMonoid D.generators a.val))
      (f : C.sharpChart (inferInstance : IsOpenImmersion
        ((logOpenEtale V.scheme).obj D.U).hom) a ⟶
          FineFan.affine (logIdealSaturatedChartMonoid D.generators a.val))
      (g : b.SharpSpaceMap),
      FineFan.IsLocalMorphism f ∧
      (∀ x, Function.Bijective (FineFan.stalkMap (f ≫ K.inclusion) x)) ∧
      (f ≫ K.inclusion) ≫ β.map =
        C.sharpChartInclusion (inferInstance : IsOpenImmersion
          ((logOpenEtale V.scheme).obj D.U).hom) a ≫ g.map ≫ c.map ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ Spec (.of (logIdealTensorRing D.A
          (D.idealChart h).alpha
          (logIdealSaturatedChartInclusion D.generators a.val)))),
        ∃ (eF : FineFan.stalk F'.space.presheaf
            (K.inclusion.hom.base (f.hom.base (t default))) ≃*
              Associates (Algebra.faceLocalization
                (logIdealSaturatedChartMonoid D.generators a.val)
                (logChartUnitFace (C.ringChart a) (t default))))
          (eN : Associates (Algebra.faceLocalization
              (logIdealSaturatedChartMonoid D.generators a.val)
              (logChartUnitFace (C.ringChart a) (t default))) ≃*
            V'.logStructure.characteristic
              (t ≫ C.toPullback a ≫ pullback.fst b.base
                ((logOpenEtale V.scheme).obj D.U).hom))
          (e : FineFan.stalk (C.sharpChart (inferInstance : IsOpenImmersion
              ((logOpenEtale V.scheme).obj D.U).hom) a).presheaf (t default) ≃*
            V'.logStructure.characteristic
              (t ≫ C.toPullback a ≫ pullback.fst b.base
                ((logOpenEtale V.scheme).obj D.U).hom)),
          C.IsGeometricComparison (inferInstance : IsOpenImmersion
            ((logOpenEtale V.scheme).obj D.U).hom) a t e ∧
          (∀ q : logIdealSaturatedChartMonoid D.generators a.val,
            ∃ (r : Algebra.faceLocalization
                (logIdealSaturatedChartMonoid D.generators a.val)
                (logChartUnitFace (C.ringChart a) (t default)))
              (s : FineFan.stalk F'.space.presheaf
                (K.inclusion.hom.base (f.hom.base (t default)))),
              r.val = Algebra.GrothendieckGroup.of q ∧
              FineFan.stalkMap K.inclusion (f.hom.base (t default)) s =
                FineFan.affineGerm (f.hom.base (t default)) q ∧
              eF s = Associates.mk r ∧
              eN (Associates.mk r) = Associates.mk
                (V'.logStructure.toEtalePrelogStructure.germ
                  (t ≫ C.toPullback a ≫ pullback.fst b.base
                    ((logOpenEtale V.scheme).obj D.U).hom)
                  (@Scheme.Etale.mk _ _
                    (C.toPullback a ≫ pullback.fst b.base
                      ((logOpenEtale V.scheme).obj D.U).hom) (C.etale a))
                  (Over.homMk t) (C.chart a q))) ∧
          ∀ s, e (FineFan.stalkMap (f ≫ K.inclusion) (t default) s) = eN (eF s) := by sorry

end AlgebraicGeometry
