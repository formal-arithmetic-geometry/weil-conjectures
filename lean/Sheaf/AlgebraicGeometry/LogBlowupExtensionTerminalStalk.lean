/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure

/-!
# Terminal characteristic stalks of an extended log blowup procedure

Source: ILO, Exposé VIII, 3.3.8--3.3.13 and the descent reduction in the proof of
Theorem 3.3.15, pp. 107--110
(blueprint: lem-trf-log-blowup-extension-terminal-stalk).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A terminal geometric characteristic stalk of an extended procedure occurs, up
to monoid isomorphism, on a charted test input. This is independent of any smoothness
or freeness assertion about the procedures.

Source: ILO VIII, 3.3.8--3.3.13 and proof of Theorem 3.3.15, pp. 107--110
(blueprint: lem-trf-log-blowup-extension-terminal-stalk).

Proof:
1. Choose the finite quasi-compact strict étale fan-chart cover of X supplied by
`log_fan_chart_blowup`. Each member Y is an admissible charted input: strictness
identifies its geometric characteristic stalks with those on X, so torsion-freeness
transfers. This includes the empty cover of an empty scheme.
2. For each member, take the assumed contracted-pullback comparison between E(X)
and T(Y). Expand T(Y) by repeating the levels at the deleted stages. The comparison
data give an fs Cartesian square at every step, with the pulled ideal as center.
3. Inductively these squares are ordinary scheme pullback squares and their level
maps are strict étale. Indeed, strict pullback of a log blowup is computed by the
same saturated chart tensor rings, by `coherentLogIdeal_chart_construction`.
Uniqueness in the fs Cartesian property identifies the supplied squares with these
canonical squares. At a deleted whole center the blowup is the log identity by
its universal property, so the same assertion holds for a repeated level.
4. Ordinary scheme base change preserves jointly surjective étale families. Apply
this at each of the finitely many stages. The last-index equation of each comparison
identifies its final repeated level with the terminal level of T(Y). Those terminal
levels therefore form a jointly surjective strict étale cover of the terminal E(X).
5. The specified geometric point t lifts to some member of this cover over the same
algebraically closed field: its fiber is a nonempty étale scheme over that field,
and an affine neighbourhood of a point in that fiber has a rational closed point.
Let s be that lift. Strictness gives the canonical multiplicative isomorphism from
the characteristic at its composite to the characteristic at s. Transport along
the equality of that composite with t to obtain the required isomorphism.
6. There is no point t when the terminal scheme is empty. Length zero needs no
induction steps, and consecutive deletions only repeat levels, leaving the argument
unchanged. No assumption about free monoids or a chosen fan resolution was used. -/
theorem log_blowup_extension_terminal_stalk
    (T : StrictEtaleLogBlowupProcedure IsChartedLogBlowupInput.{u})
    (E : StrictEtaleLogBlowupProcedure IsLogBlowupInput.{u})
    (hCompare : ∀ (X Y : FineSaturatedLogScheme.{u}) (hX : IsLogBlowupInput X)
      (hY : IsChartedLogBlowupInput Y) (f : EtaleLogHom Y X),
      f.IsStrict → Etale f.base →
        Nonempty (LogBlowupComparison f (E.tower X hX) (T.tower Y hY)))
    (X : FineSaturatedLogScheme.{u}) (hX : IsLogBlowupInput X)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶
      ((E.tower X hX).tower.level (Fin.last (E.tower X hX).tower.length)).scheme) :
    ∃ (Y : FineSaturatedLogScheme.{u}) (hY : IsChartedLogBlowupInput Y)
      (s : Spec (.of Ω) ⟶
        ((T.tower Y hY).tower.level (Fin.last (T.tower Y hY).tower.length)).scheme),
      Nonempty
        (((E.tower X hX).tower.level
            (Fin.last (E.tower X hX).tower.length)).logStructure.characteristic t ≃*
          ((T.tower Y hY).tower.level
            (Fin.last (T.tower Y hY).tower.length)).logStructure.characteristic s) := by sorry

end AlgebraicGeometry
