/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.ModuliNormalizationTests
public import Sheaf.AlgebraicGeometry.FormalModuliQuotient
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.ModuliStackProperties
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic

import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleOpenIntegralClosure
import WeilConjectures.RingTheory.IntegralClosureFiniteNormalProduct
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Smooth.IntegralClosure
import Sheaf.TraceFormula.EtaleNormalDomainFiniteFactors
import Sheaf.RingTheory.GeometricallyNormalPerfectClosureCriterion
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.RingTheory.CompletionFiniteExtension
import Sheaf.RingTheory.ExcellentRing
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.RingTheory.NormalOfFlatNormalFibers
import WeilConjectures.RingTheory.FiniteProductNormal

/-! # Finite normalization of a smooth DM stack and its charts

Source: Stacks, Tags 0ABP, 0BB0 and 038O; Pikaart--de Jong, §2.3.6, printed p.11
(blueprint: lem-sfb-dm-finite-normalization-charts).

The first statement constructs the normalization, including its étale-chart and
perfect-field scalar-extension clauses. The second gives the formal-chart clause
for that same normalization after passage to an algebraically closed field. The
scalar-extension clause identifies this with the scalar extension of the original
normalization. Formal quotients use the torsor atlas-and-arrows test, not orbit sets.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃ v₄ w₄

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite normalization in the entire cover of a dense open. All chart components
are retained by the relative integral-closure construction, and the specified map
from the cover fixes its descent comparisons. Over a perfect field the same chart
construction commutes with every extension field, including the identity extension.

Source: Stacks 0ABP, 0BB0 and 038O; Pikaart--de Jong §2.3.6
(blueprint: lem-sfb-dm-finite-normalization-charts).

Proof plan:
1. Smooth charts are normal (lem-trf-smooth-geometrically-normal). Split their finitely
   many normal components (lem-trf-normal-topologically-noetherian-components). The
   cover has normal components (lem-fin-etale-normal-components). Flat density
   (lemma-nagata-dense-flat-pullback) and the finite étale field-algebra decomposition
   identify all generic fields (lem-weil-pbc-etale-algebra-over-field-product).
2. On affine chart opens form the integral closure in their product. It equals the
   closure in sections of the open cover. The finite-etale-open integral-closure and
   finite-normal-product lemmas give finiteness and normality. Localization glues
   these models (lem-weil-pbc-integral-closure-commutes-localization); the fraction-field
   clause is lem-weil-pbc-integral-closure-finite-extension-normal.
3. On the dense open a finite étale normal algebra is its own integral closure in
   its total rational algebra, including the zero algebra. Thus the restriction is V.
4. lem-sfb-integral-closure-etale-base-change identifies the chart pullbacks. The
   generic factors are identified by lem-trf-etale-normal-domain-finite-factors and
   flat density. Canonical inclusions agree on triple overlaps; effective finite
   descent (lem-sfb-finite-schemes-etale-stack-descent) gives N and its finite map.
5. Over a perfect field, lem-weil-pbc-geometrically-normal-perfect-closure-criterion
   keeps every chart model normal after any scalar extension. Flat density retains
   all generic factors, including splitting factors. A finite normal algebra in this
   rational algebra is its integral closure. The canonical identifications descend.
-/
theorem exists_dm_finite_normalization_charts (k : Type u) [Field k]
    (X : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (U : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (V : BasedCategory.{v₃, w₃} (Over (Spec (.of k))))
    (j : BasedFunctor U X) (v : BasedFunctor V U)
    (hX : IsDeligneMumfordModuliStack X) (hXs : HasSmoothFiniteTypeModuliAtlas X)
    (hU : IsModuliStack U) (hV : IsModuliStack V)
    (hj : IsDenseOpenModuliMap j) (hv : IsRepresentableFiniteModuliMap v)
    (hve : IsEtaleModuliMap v) :
    ∃ (N : BasedCategory.{max u v₁ v₂ v₃, max (u + 1) w₁ w₂ w₃}
        (Over (Spec (.of k)))) (ν : BasedFunctor N X) (i : BasedFunctor V N)
        (e : v.comp j ≅ i.comp ν),
      IsDeligneMumfordModuliStack N ∧ IsNormalModuliStack N ∧
      IsRepresentableFiniteModuliMap ν ∧
      IsModuliChartNormalization (v.comp j) ν i e.symm ∧
      (moduliTwoFiberLift v i e).toFunctor.IsEquivalence ∧
      (PerfectField k → ModuliNormalizationScalarCharts (v.comp j)) := by
  sorry

/-- The formal-chart clause, on the normalization over an algebraically closed
field. The model is the explicit relative normalization of the entire pulled-back
cover; its affine coordinate ring is the stated integral closure B. The lifted
coherent action is required to intertwine the original action through the specified
base-change equivalence. Its quotient therefore identifies the entire completion
above the residual gerbe, and its geometric automorphisms are the stabilizers.

Source: Pikaart--de Jong §2.3.6, printed p.11; Stacks 0DQZ, 0C23, 04M9 and 044W
(blueprint: lem-sfb-dm-finite-normalization-charts).

Proof plan:
6. lem-sfb-effective-formal-chart-completed-atlas identifies R with the completed local
   ring A of an étale chart. Pull back the finite normal chart algebra C. Excellence
   of fields and finite-type localizations (lem-exc-fields-excellent and
   lem-exc-finite-type-localization-excellent), the finite-algebra completion theorem
   (lem-weil-pbc-completion-finite-extension), and the G-ring completion theorem give
   a product of completed normal local rings. G-ring fibres are geometrically regular;
   taking the trivial purely inseparable extension makes them regular and hence normal
   (lem-weil-pbc-regular-ring-normal). The completion is Noetherian, and flat normal
   fibres preserve normality (lem-weil-pbc-flat-normal-fibres-noetherian-normal).
   Finite products are normal (lem-weil-pbc-finite-product-normal).
7. The pullback open is the whole cover E and remains schematically dense by flatness
   of completion and lemma-nagata-dense-flat-pullback. The finite normal algebra thus
   has exactly all rational fields of E. Integrality in that rational algebra identifies
   it with B, not with an arbitrary-base-change integral closure.
8. lem-sfb-finite-formal-quotient-pullback identifies the completion with the quotient
   of this finite algebra. Its action is the descent action; the arrows extend those
   on the open because equality holds in the total rational algebra. This also gives
   the displayed equivariance of the comparison with the original formal chart.
9. At a closed geometric point b the residue field is Ω, since it is finite over Ω.
   An arrow from b to itself in the quotient is exactly an h fixing b; composition is
   group multiplication. If B is zero there are no such b. The field-extension clause
   of exists_dm_finite_normalization_charts transports this assertion to N_Ω.
-/
theorem dm_finite_normalization_formal_chart (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (X : BasedCategory.{v₁, w₁} (Over (Spec (.of Ω))))
    (U : BasedCategory.{v₂, w₂} (Over (Spec (.of Ω))))
    (V : BasedCategory.{v₃, w₃} (Over (Spec (.of Ω))))
    (N : BasedCategory.{v₄, w₄} (Over (Spec (.of Ω))))
    (j : BasedFunctor U X) (v : BasedFunctor V U) (ν : BasedFunctor N X)
    (i : BasedFunctor V N) (e : i.comp ν ≅ v.comp j)
    (hX : IsDeligneMumfordModuliStack X) (hXs : HasSmoothFiniteTypeModuliAtlas X)
    (hU : IsModuliStack U) (hV : IsModuliStack V)
    (hj : IsDenseOpenModuliMap j) (hv : IsRepresentableFiniteModuliMap v)
    (hve : IsEtaleModuliMap v) (hN : IsDeligneMumfordModuliStack N)
    (hn : IsNormalModuliStack N) (hν : IsRepresentableFiniteModuliMap ν)
    (hchart : IsModuliChartNormalization (v.comp j) ν i e)
    (R : Type u) [CommRing R] [Algebra Ω R] [IsRegularLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (Q : Over (Spec (.of Ω))) (qR : Q.left ≅ Spec (.of R))
    (hQR : Q.hom = qR.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω R)))
    (σ : Over.mk (𝟙 (Spec (.of Ω))) ⟶ Q)
    (hσ : ∀ z : Spec (.of Ω), qR.hom (σ.left z) = IsLocalRing.closedPoint R)
    (f : BasedFunctor (discreteModuli (yoneda.obj Q)) X)
    (H : Type u) [Group H] [Finite H] (ρ : H →* Aut Q) (θ : ModuliAtlasAction ρ f)
    (hf : IsFormalModuliQuotient ρ f θ
      {z | qR.hom z = IsLocalRing.closedPoint R}
      (fun _ t ↦ ModuliCompletionAt (moduliChartMap σ f) t))
    (E : Over (Spec (.of Ω))) (p : E ⟶ Q) [QuasiCompact p.left]
    [QuasiSeparated p.left]
    (c : BasedFunctor (discreteModuli (yoneda.obj E))
      (moduliTwoFiberProduct f (v.comp j)))
    (hc : IsSchemeModuliBaseChange c p) :
    ∃ (b : BasedFunctor
        (discreteModuli (yoneda.obj (AlgebraicGeometry.Over.normalization p))) N)
        (β : b.comp ν ≅ moduliChartMap (AlgebraicGeometry.Over.fromNormalization p) f)
        (ρB : H →* Aut (AlgebraicGeometry.Over.normalization p))
        (θB : ModuliAtlasAction ρB b),
      IsFinite p.left.fromNormalization ∧
      IsAdicComplete ((IsLocalRing.maximalIdeal R).map
        ((Scheme.ΓSpecIso (.of R)).inv ≫ qR.hom.appTop ≫
          p.left.fromNormalization.appTop).hom) Γ(p.left.normalization, ⊤) ∧
      (moduliTwoFiberLift
        (discreteModuliMap (yoneda.map (AlgebraicGeometry.Over.fromNormalization p)))
        b β.symm).toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso
        ((discreteModuliMap (yoneda.map (AlgebraicGeometry.Over.toNormalization p))).comp
          (moduliTwoFiberLift
            (discreteModuliMap (yoneda.map (AlgebraicGeometry.Over.fromNormalization p)))
            b β.symm))
        (c.comp (moduliTwoFiberMapRight f i e))) ∧
      (∀ h : H, (ρB h).hom ≫ AlgebraicGeometry.Over.fromNormalization p =
        AlgebraicGeometry.Over.fromNormalization p ≫ (ρ h).hom) ∧
      (∀ h : H, ∃ ε :
          (moduliChartMap (ρB h).hom
            (moduliChartMap (AlgebraicGeometry.Over.fromNormalization p) f)).toFunctor =
          (moduliChartMap (AlgebraicGeometry.Over.fromNormalization p)
            (moduliChartMap (ρ h).hom f)).toFunctor,
        HEq ((Functor.whiskerRight (θB.arrow h).val.hom ν.toFunctor) ≫ β.hom.toNatTrans)
          ((Functor.whiskerLeft
            (discreteModuliMap (yoneda.map (ρB h).hom)).toFunctor β.hom.toNatTrans) ≫
            eqToHom ε ≫ Functor.whiskerLeft
              (discreteModuliMap
                (yoneda.map (AlgebraicGeometry.Over.fromNormalization p))).toFunctor
              (θ.arrow h).val.hom)) ∧
      IsFormalModuliQuotient ρB b θB
        {z | qR.hom (p.left.fromNormalization z) = IsLocalRing.closedPoint R}
        (fun _ t ↦ ModuliCompletionAt (moduliChartMap σ f) (t.comp ν)) ∧
      ∀ (z : Over.mk (𝟙 (Spec (.of Ω))) ⟶ AlgebraicGeometry.Over.normalization p),
        (∀ a : Spec (.of Ω),
          qR.hom (p.left.fromNormalization (z.left a)) = IsLocalRing.closedPoint R) →
        ∃ ε : Aut (moduliChartPoint (moduliChartMap z b)) ≃*
            @MulAction.stabilizer H
              (Over.mk (𝟙 (Spec (.of Ω))) ⟶ AlgebraicGeometry.Over.normalization p) _
              (moduliChartPointAction ρB _) z,
          ∀ a : Aut (moduliChartPoint (moduliChartMap z b)),
            HEq a.hom.val
              (((θB.arrow (ε a).val).val.inv).app
                (CostructuredArrow.mk (yoneda.map z))) := by
  sorry

end AlgebraicGeometry
