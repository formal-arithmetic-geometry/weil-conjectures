/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelPresentation

/-! # Marked tests with intervening open restrictions

Source: BMT, arXiv:0905.3580, sections 5.1--5.2, and the local-test convention in
ILO VIII 2.3.13 (blueprint: def-trf-restricted-marked-tests).
The existing one-step relation supplies all three geometric tests and their transforms.
Only the missing open-restriction case is added here.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.HilbertSamuel

/-- Agreement through finite depth, including open restrictions at every intermediate stage.
`EquivalentThrough 1` supplies cosupport equality and existence of both transforms for every
allowed geometric step. The second clause continues those same transforms; the last clause
adds cartesian restriction of the supports, ideals and ordered boundary.
Source: BMT 5.1--5.2 and the local convention of the coefficient-restriction lemma
(blueprint: def-trf-restricted-marked-tests). -/
noncomputable def RestrictedEquivalentThrough {k : Type u} [Field k] :
    ℕ → (S : Embedded k) → Marked S → Marked S → Prop
  | 0, _, M, P => M.cosupport = P.cosupport
  | n + 1, S, M, P => EquivalentThrough 1 S M P ∧
      (∀ (T : Embedded k) (s : Step S T) (M' P' : Marked T),
        s.Admissible M.cosupport → s.Transforms M M' → s.Transforms P P' →
          RestrictedEquivalentThrough n T M' P') ∧
      (∀ (T : Embedded k) (f : T.Z ⟶ S.Z), IsOpenImmersion f →
        f ≫ S.p = T.p → T.boundary = S.boundary.map (fun I ↦ I.comap f) →
        (∃ M' : Marked T, MarkedPullback f M M') ∧
        (∃ P' : Marked T, MarkedPullback f P P') ∧
        ∀ (M' P' : Marked T), MarkedPullback f M M' → MarkedPullback f P P' →
          RestrictedEquivalentThrough n T M' P')

/-- Equality of cosupports, permissible centers and subsequent cosupports for every finite
word in the three existing tests and open restrictions. Source: BMT 5.2, with the explicit
open-restriction convention of the coefficient-restriction lemma
(blueprint: def-trf-restricted-marked-tests). -/
noncomputable def RestrictedEquivalent {k : Type u} [Field k] {S : Embedded k}
    (M P : Marked S) : Prop :=
  ∀ n : ℕ, RestrictedEquivalentThrough n S M P

end AlgebraicGeometry.HilbertSamuel
