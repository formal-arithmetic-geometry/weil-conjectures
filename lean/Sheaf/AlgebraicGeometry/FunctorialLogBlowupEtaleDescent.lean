/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
import Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure
import Sheaf.AlgebraicGeometry.FiniteCoproductLfpQcqs
import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction
import Sheaf.CategoryTheory.SetSheafCoverDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

/-!
# Étale descent of finite functorial log blowup procedures

Source: ILO VIII, proof of Theorem 3.3.15, pp. 109--110, with the effective
stagewise gluing of centers using VIII 3.3.7--3.3.10
(blueprint: lem-trf-functorial-log-blowup-etale-descent).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- A chart-independent finite rule with coherent ordered centers descends uniquely,
with its strict étale contracted-pullback comparisons. The charted domain includes
finite disjoint unions, and its comparisons include their component inclusions.

Source: ILO VIII, proof of Theorem 3.3.15, pp. 109--110
(blueprint: lem-trf-functorial-log-blowup-etale-descent).

Proof:
1. The identity comparison identifies an assigned tower with its contraction, so no
whole-monoid center occurs. A whole-monoid blowup is the identity by its universal
property; a proper principal center is not removed. The empty input has length zero.
2. Choose a finite quasi-compact strict étale chart cover by
`lem-trf-log-fan-chart-blowup`. Its finite disjoint union is another charted input,
using `lem-weil-pbc-scheme-coproduct-family`,
`lem-weil-pbc-finite-coproduct-lfp-qcqs`, and `def-trf-fine-fan-blowup`.
Use its one prescribed finite ordered tower, of length n, to synchronize all centers.
3. Double and triple overlaps are quasi-compact by locally Noetherian
quasi-separatedness and `lem-weil-pbc-qcqs-morphism-permanence`; they are locally
Noetherian by `pqf-lem-locnoeth-lft`. Strict pullback gives their fan charts and
characteristic stalks. The same applies to common refinements and strict étale tests.
4. At every tower stage, pullback along a surjective strict étale cover remains a
surjective strict étale cover by `lem-weil-pbc-etale-covering-base-change` and the
strict compatibility of `lem-trf-coherent-log-ideal-chart-construction`.
A pulled ideal is whole exactly when the original is whole, by the sheaf condition.
Thus these covers remove no stages of a contracted tower.
5. The comparisons on both overlap projections identify the full length-n towers.
Their centers agree, and the composition and identity laws give the cocycle and
diagonal laws on triple overlaps, with the same ordered index set at every stage.
6. Descend each center as a subsheaf of the log monoid sheaf, inductively in i.
Use `lem-pe-set-sheaf-cover-descent`, `lem-weil-pbc-etale-site-localization-open`,
and the small-site convention `def-weil-size-convention`. A section belongs to the
descended ideal precisely when it belongs after the cover. This proves uniqueness,
injectivity into the log sheaf and ideal stability. Nonempty finite local generators
descend the nonempty coherence condition of `def-trf-fs-log-blowup`.
7. Apply `lem-trf-coherent-log-ideal-chart-construction` to the descended ideal.
Its universal blowup agrees with the specified local stage. Repeat for all n stages.
No descended center is whole, since its restriction is proper. This constructs the
finite global tower and its unchanged pullback to the surjective chart cover.
8. Compare two choices on their common refinement. The centers coincide there,
hence coincide globally by the sectionwise membership description. The universal
blowup property gives a unique isomorphism at each level. Induction gives the
canonical isomorphism of towers with centers and its cocycle law.
9. For any strict étale Y → X, use the chart cover pulled back to Y. Whole centers
are detected on that cover, so exactly the same stages, including consecutive ones,
are deleted before and after descent. The remaining centers and blowups agree.
Identity and composition laws hold on the cover and therefore globally by uniqueness.
10. On a charted input take its identity cover, obtaining its prescribed tower.
Consequently every chart neighbourhood has the prescribed contracted pullback.
Any other compatible extension has the same centers after a surjective chart cover.
Descend their equalities and use uniqueness of each universal blowup inductively.
The resulting unique isomorphisms preserve centers and every comparison. -/
theorem functorial_log_blowup_etale_descent
    (T : StrictEtaleLogBlowupProcedure IsChartedLogBlowupInput.{u}) :
    ∃ E : StrictEtaleLogBlowupProcedure IsLogBlowupInput.{u},
      Nonempty (LogBlowupProcedureAgreement T E (fun _ h ↦ h.1)) ∧
      (∀ (X Y : FineSaturatedLogScheme.{u}) (hX : IsLogBlowupInput X)
        (hY : IsChartedLogBlowupInput Y) (f : EtaleLogHom Y X),
        f.IsStrict → Etale f.base →
          Nonempty (LogBlowupComparison f (E.tower X hX) (T.tower Y hY))) ∧
      ∀ E' : StrictEtaleLogBlowupProcedure IsLogBlowupInput.{u},
        Nonempty (LogBlowupProcedureAgreement T E' (fun _ h ↦ h.1)) →
          Nonempty (Unique (LogBlowupProcedureAgreement E E' (fun _ h ↦ h))) := by
  sorry

end AlgebraicGeometry
