/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.GluedLimitComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Properties of the final Noetherian base system

Source: Weil conjectures blueprint, chapter `sec-nagata-compactification`, unit
`sk-cor-nagata-sketch-fp`, lemma "Properties of the final Noetherian base system"
(blueprint: lemma-nagata-final-noetherian-base-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.NoetherianApproximation

/-- Every stage of the final base system is Noetherian and of finite type over the integers,
every transition is affine, and the retained limit comparison is an isomorphism.

Source: Weil conjectures blueprint, `sk-cor-nagata-sketch-fp`, lemma "Properties of the final
Noetherian base system" (blueprint: lemma-nagata-final-noetherian-base-system).

Proof: apply `prop-nagata-noetherian-inverse-system` to the supplied approximation `N` of the
quasi-compact quasi-separated base, identified with the final system by
`def-nagata-final-noetherian-base-system`. Its stages have finite type over the integers and
its transitions are affine. Its limit cone identifies the base with the inverse limit, so
`N.gluedLimitComparison` is an isomorphism. Finally every stage is Noetherian by
`def-nagata-noetherian-inverse-system`, as recorded by `N.isNoetherian_obj`.
The `HasLimit` instance selects a limit; existence is already supplied by `N.isLimit`. -/
theorem finalBaseSystem_properties {S : Scheme.{u}} (N : S.NoetherianApproximation)
    [HasLimit N.D] :
    (∀ i : N.I, IsNoetherian (N.D.obj i) ∧
      LocallyOfFiniteType (specULiftZIsTerminal.from (N.D.obj i)) ∧
      QuasiCompact (specULiftZIsTerminal.from (N.D.obj i))) ∧
    (∀ (i j : N.I) (f : i ⟶ j), IsAffineHom (N.D.map f)) ∧
    IsIso N.gluedLimitComparison := by
  sorry

end AlgebraicGeometry.Scheme.NoetherianApproximation
