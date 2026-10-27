/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure

/-!
# The fan resolution procedure on globally charted log schemes

Source: ILO, Exposé VIII, 3.3.13 and proof of Theorem 3.3.15, pp. 108--110
(blueprint: lem-trf-charted-fan-resolution-procedure).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A fixed functorial fan resolution induces a chart-independent strict étale
procedure on globally fan-charted inputs. Its terminal level still has a chart to a
terminal fan of the fixed resolution, with the geometric-stalk comparisons.

Source: ILO VIII, Remark 3.3.13(i),(iii) and proof of Theorem 3.3.15, pp. 108--110
(blueprint: lem-trf-charted-fan-resolution-procedure).

Proof:
1. For a globally charted admissible input, cover its quasi-compact image in the
fan by finitely many affine localization neighbourhoods. The characteristic-stalk
isomorphisms identify their monoids with sharp fs characteristic monoids. Their
group completions are torsion free. Restrict the target fan to their union, which
therefore gives a `ResolutionInput`. The empty input uses the empty fan.
2. Apply the supplied resolution to that fan. Lift its finite ordered tower by
`log_fan_chart_blowup`, pulling each fan ideal back to the log ideal specified there.
Every lifted stage is a saturated log blowup along a nonempty coherent log ideal.
3. Delete exactly the stages whose pulled ideal is the whole log monoid sheaf.
The identity principalizes that ideal under every log morphism. The universal
property therefore identifies each deleted blowup with the identity log scheme,
including its section maps. Contracting finitely many stages preserves the final
log scheme up to a log isomorphism. Transport the final fan chart and its normalized
geometric-stalk comparisons through that isomorphism. No proper principal center
is deleted, and a zero-length tower is allowed.
4. Compare two charts using `strict_fan_chart_local_comparison` for the identity.
On each comparison neighbourhood the charts factor through isomorphic affine
localizations. The supplied fan resolution is functorial for these localizations
and isomorphisms. Pull back its identified ordered centers. Universal log blowups
give the unique level comparisons over the preceding level, preserving centers.
These comparisons agree on overlaps and satisfy the cocycle identity, so the
contracted local towers glue to one tower independent of the selected chart.
5. Repeat the comparison for an arbitrary strict étale map between charted inputs.
Strict base change of lifted fan towers identifies their centers; fan functoriality
and deletion of exactly whole centers give the required contraction indices and
Cartesian squares. Uniqueness at each universal blowup proves the identity and
composition equations on both indices and section maps.
6. Use the same comparisons for component inclusions into finite disjoint unions.
They synchronize the ordered centers with the resolution of the disjoint union fan.
Thus the rule is a `StrictEtaleLogBlowupProcedure` on the charted domain, which is a
property of the input and makes no selected chart part of that input. The terminal
charts and comparisons constructed in step 3 give the displayed conclusion. -/
theorem exists_charted_fan_resolution_procedure
    (R : FineFan.SmoothFunctorialDesingularization.{u}) :
    ∃ T : StrictEtaleLogBlowupProcedure IsChartedLogBlowupInput.{u},
      ∀ (X : FineSaturatedLogScheme.{u}) (hX : IsChartedLogBlowupInput X),
        ∃ (F : FineFan.ResolutionInput.{u})
          (c : LogFanChart
            ((T.tower X hX).tower.level (Fin.last (T.tower X hX).tower.length))
            ((R.resolution F).tower.level (Fin.last (R.resolution F).length))),
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (t : Spec (.of Ω) ⟶
              ((T.tower X hX).tower.level (Fin.last (T.tower X hX).tower.length)).scheme),
            ∃ e : FineFan.stalk
                ((R.resolution F).tower.level (Fin.last (R.resolution F).length)).space.presheaf
                (c.map.hom.base (t default)) ≃*
                ((T.tower X hX).tower.level
                  (Fin.last (T.tower X hX).tower.length)).logStructure.characteristic t,
              c.IsGeometricComparison t e := by sorry

end AlgebraicGeometry
