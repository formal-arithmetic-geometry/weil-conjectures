/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.PoincareDuality.Poincare
public import Sheaf.Targets.SmoothPurityQbar
public import Sheaf.Targets.PoincareTateBoundedConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Poincaré duality as the trace of the compact-support cup product

Source: `WeilConjectures/PoincareDuality/Poincare.lean`, `uncurry_poincareMap`;
blueprint `sec-six-functors/sk-thm-sf-identification`, first proof paragraph
(blueprint: nt-target-poincare-uncurry).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The transpose of Poincaré duality is the compact-support cup product followed by trace.

Source: `WeilConjectures/PoincareDuality/Poincare.lean`, `uncurry_poincareMap`;
blueprint `sec-six-functors/sk-thm-sf-identification`, first proof paragraph
(blueprint: nt-target-poincare-uncurry).

Proof plan:
1. Put F = Rp_!, R = Rp^!, U = Lp^*, V = Rp_*, A = the unit on X, B = the unit on S,
   T = the shifted Tate twist and D = R(B). With theta = purity inverse and
   j = curry of the left unitor on D, the Poincaré map is V(theta ≫ j) followed by
   Verdier exchange. Use uncurry precomposition and uncurry-curry cancellation
   (`lem-pod-closed-uncurry-laws`) to expand its transpose into projection,
   the U-V counit, evaluation and the F-R counit.
2. Naturality of projection at V(theta ≫ j) and of the U-V counit moves this map
   through the pairing. Functoriality rewrites the result as projection followed by
   F of the U-V counit, F of tensoring theta ≫ j, evaluation and the F-R counit.
3. The evaluation formula and uncurry-curry cancellation
   (`lem-pod-closed-uncurry-laws`) identify tensoring j followed by evaluation with
   the left unitor. Naturality of that unitor (`def-sfb-monoidal-category`) moves
   theta past it. The first three factors are cupProduct and the last two trace.
   All factors retain their displayed order; no tensor symmetry is applied. -/
theorem uncurry_poincareMap_of_smooth
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] {X S : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (p : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d p.left] :
    uncurry (poincareMap ℓ p d) = cupProduct ℓ p d ≫ trace ℓ p d :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
