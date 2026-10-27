/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FanCenterTensorChartData
import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction
import Sheaf.AlgebraicGeometry.FanCenterPullbackCoherence
import Sheaf.AlgebraicGeometry.FanCenterBlowupZariski
import Sheaf.AlgebraicGeometry.FanCenterTensorChartComparison

/-!
# Inverse-image fan centers and local saturated log blowup charts

Source: ILO VIII 3.1.19--3.1.25, 3.3.7--3.3.9, 3.3.13(i),(iii)
(blueprint: lem-trf-fan-center-local-blowup-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Coherent inverse-image centers, existence of their saturated log blowups and every
specified local tensor-chart comparison, including the normalized stalk identifications.

Source: ILO VIII 3.1.19--3.1.25, 3.3.7--3.3.9, 3.3.13(i),(iii)
(blueprint: lem-trf-fan-center-local-blowup-charts).

Proof:
1. Use lem-trf-fan-chart-local-monoid-lift and lem-trf-fine-fan-point-localization
near each point to lift the sharp fan stalk and choose finite nonempty generators E.
Equality modulo log units shows the inverse-image ideal is exactly (h(e):e in E)N.
This proves coherence and the same equality on every chart supplied in the statement.
2. Apply lem-trf-coherent-log-ideal-chart-construction to this ideal. Its fs universal
object is the saturated blowup. On each affine open its charts are precisely the
saturated fraction monoids R_a and the rings A tensor over Z[P] with Z[R_a].
3. Each R_a is finitely generated. A polynomial algebra over the Noetherian A surjects
onto its tensor ring by sending variables to generating monomials. Finite-type
Noetherian permanence makes all charts Noetherian and hence the blowup locally so.
4. Apply lem-trf-monoid-chart-characteristic-fan on each chart. Its Zariski associated
log structures agree on overlaps: R_a[(b/a)^-1] = R_b[(a/b)^-1] inside P^gp, since
saturation commutes with localization. Adjoining inverses of sections mapping to units
does not change associated logs. The inclusions give the triple cocycle, so these glue.
5. The corresponding fan blowup chart is S(R_a). Compose its chart map with its open
inclusion. Both composites to F pull every p to the characteristic of h(p);
lem-trf-affine-fan-hom-universal identifies these morphisms. The unit-face calculation
of lem-trf-monoid-chart-characteristic-fan identifies both stalks with (R_a)_H/H^gp,
with the stated normalization, and gives the inverse-image sheaf isomorphism.
-/
theorem fan_center_local_blowup_charts
    (V : FineSaturatedLogScheme.{u}) (F : FineFan.Fan.{u})
    (c : LogFanChart V F) (J : FineFan.IdealFamily F)
    (hJ : FineFan.IsNonemptyCoherentIdeal J) :
    V.logStructure.IsNonemptyCoherentIdeal (c.pullbackIdeal J) ∧
    ∃ (V' : FineSaturatedLogScheme.{u}) (b : EtaleLogHom V' V),
      IsSaturatedLogBlowup b (c.pullbackIdeal J) ∧ V'.logStructure.IsZariski ∧
      ∀ D : c.AffineCenterInput J,
        ∃ h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (t : Spec (.of Ω) ⟶ V.scheme)
          (w : (Scheme.pointSmallEtale t).fiber.obj ((logOpenEtale V.scheme).obj D.U)),
          V.logStructure.idealStalk (c.pullbackIdeal J) t =
            {m | ∃ p ∈ D.generators, ∃ n : V.logStructure.toEtalePrelogStructure.stalk t,
              V.logStructure.toEtalePrelogStructure.germ t
                ((logOpenEtale V.scheme).obj D.U) w (D.chart p) * n = m},
        ∃ C : LogIdealTensorCover (D.idealChart h) b.toLogMap
            (fun a ↦ logIdealSaturatedChartMonoid D.generators a.val)
            (fun a ↦ logIdealSaturatedChartInclusion D.generators a.val),
        ∀ (F' : FineFan.Fan.{u}) (β : FineFan.Hom F' F),
          FineFan.IsSaturatedBlowup β J →
          ∀ a : {a : D.P // a ∈ D.generators},
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
                  ∀ s, e (FineFan.stalkMap (f ≫ K.inclusion) (t default) s) = eN (eF s) := by
  obtain ⟨hI, hgen⟩ := fan_center_pullback_coherence V F c J hJ
  obtain ⟨K, hK, hKqc, hKstalk, hKchart, Y₀, N₀, b₀, V', b, s,
    hb₀, hb, hfs, hcomp, huniq, hfinite, hcharts, hbase⟩ :=
      coherentLogIdeal_chart_construction V (c.pullbackIdeal J) hI
  have hz := fan_center_blowup_zariski V F c J hJ hI V' b hb
  refine ⟨hI, V', b, hb, hz, ?_⟩
  intro D
  let h := hgen D
  obtain ⟨hmon, C₀, C, r, hr⟩ := hcharts (D.idealChart h)
  refine ⟨h, C, ?_⟩
  intro F' β hβ a
  exact fan_center_tensor_chart_comparison V F c J V' b hb hz D h C F' β hβ a

end AlgebraicGeometry
