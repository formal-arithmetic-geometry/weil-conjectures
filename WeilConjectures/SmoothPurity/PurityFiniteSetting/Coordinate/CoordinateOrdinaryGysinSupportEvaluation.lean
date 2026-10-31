/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateOrdinaryGysinRealizationTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateOrdinaryGysinNormalizationTransport

/-! # Evaluation of ordinary exceptional transposes

Source: Milne, Section 9, Example 9.5; the affine-line boundary realization and
current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
finite etale-origin transport paragraph
(blueprint: lem-pur-coordinate-ordinary-gysin-support-evaluation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Evaluation of the exceptional transpose of any ordinary supported class is its
inverse normalized supported-Hom class after the canonical site comparison. The
class is arbitrary: no coordinate Kummer cocycle or localization boundary appears.

Source: Milne, Section 9, Example 9.5; affine-line boundary realization; current
blueprint, finite etale-origin transport paragraph
(blueprint: lem-pur-coordinate-ordinary-gysin-support-evaluation).

Proof: apply affine_line_boundary_realization to obtain the counit-compatible
ordinary etale chart. The inverse closed adjunct is closed direct image followed
by its ordinary exceptional counit, by the adjunct-counit identity. Transport
this equality through the canonical closed image mate and the exact site
comparison, using boundedSiteAdjunctionTranspose for its specified Hom-chain
and rho formula. The single-functor comparison, the exceptional shift comparison,
the comparison shift map and the shifted comparison unit are precisely the
factors of coordinateOrdinaryToGysin; cancel them by naturality and the counit
identity. More explicitly, the realization supplies comparisons d, eK and a
counit epsilon satisfying d.hom followed by closed image of eK.hom followed by
epsilon equals comparison of the ordinary counit followed by its shift map.
Its evaluation formula sends m to closed image of m followed by epsilon, with
the inverse single comparison in front. Substitute coordinateOrdinaryToGysin
in this formula and use that displayed counit equation. The formulas
support_spec and edge_spec identify the resulting cohomology map with D.support.
Evaluation on the constant unit identifies its
supported-Hom image with v.homMap applied to the ordinary Ext realization.
The cocycle normalization of chi gives the same identification: check it on
injective representatives, where both maps evaluate the same supported
morphism at one, and use naturality and an injective resolution to pass to the
input. Since chi is a bijection, apply its inverse to obtain the equation.
-/
theorem coordinateOrdinary_gysinSupportEvaluation (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (D : OrientationSupportData P h T)
    (chi : (proEtaleSupportHomPair P (zeroSection T)).Identification)
    (v : siteSupportHomTransport P (zeroSection T))
    (c : Ext ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (zeroSection T)).obj (P.constantEtale T)) (P.twistEtale h (Line T)) 2) :
    D.support.hom (P.gysinHomToSections h T
      (P.coordinateOrdinaryToGysin h T
        (Etale.supportedExactDerivedMap
          (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))
          (P.constantEtale T) (P.twistEtale h (Line T)) c))) =
      (chi.chi (P.coordinateProInput h (Line T)) 2).symm
        (v.homMap (hB := Scheme.isContinuous_toProEt (Line T))
          (P.coordinateEtaleInput h (Line T)) 2 c.hom) := by
  have hreal := affine_line_boundary_realization P h T aT
  rcases hreal with ⟨_, _, _, _, _, _, _, _, _, _, hAR⟩
  rcases hAR with ⟨χR, hb, eK, d, ε, heK, hd, hc, hnonempty, hforall⟩
  rcases hforall D.comparison with
    ⟨b, edge, e, hb_e, hedge, he_spec, huniq, hform, huniqf, hdelta⟩
  have hedgeD : edge = D.edge := by
    apply Iso.ext
    exact hedge.trans D.edge_spec.symm
  have hchart : e.hom = D.support.hom := by
    rw [he_spec, D.support_spec, hedgeD]
  let R : CoordinateOrdinaryGysinRealizationData P h T D :=
    { chi := χR
      e := e
      epsilon := ε
      hb := hb
      eK := eK
      d := d
      eK_spec := heK
      d_spec := hd
      counit_eq := hc
      chart_eq := hchart
      evaluation := hform }
  have hnorm := coordinateOrdinary_gysinSupportEvaluation_normalization
    P h T aT D R chi c
  have hsite := coordinateOrdinary_gysinSupportEvaluation_realization
    P h T aT D R v c
  have htotal :
      (chi.chi (P.coordinateProInput h (Line T)) 2)
          (D.support.hom (P.gysinHomToSections h T
            (P.coordinateOrdinaryToGysin h T
              (Etale.supportedExactDerivedMap
                (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))
                (P.constantEtale T) (P.twistEtale h (Line T)) c)))) =
        v.homMap (hB := Scheme.isContinuous_toProEt (Line T))
          (P.coordinateEtaleInput h (Line T)) 2 c.hom := by
    rw [← R.chart_eq]
    exact hnorm.trans hsite
  exact ((chi.chi (P.coordinateProInput h (Line T)) 2).symm_apply_eq.mpr htotal.symm).symm

end WeilConjectures.PurityFiniteSetting
