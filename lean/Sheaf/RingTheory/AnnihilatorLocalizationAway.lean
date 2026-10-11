/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Annihilators of finite modules localized away from an element

Source: Stacks Project, Algebra, Lemma 07T8, second assertion specialized to localization
(blueprint: lem-weil-pbc-annihilator-localization-finite).
-/

@[expose] public section

universe u v

namespace Module

/-- The annihilator of a finite module commutes with localization away from an element.
Source: Stacks Project, Algebra, Lemma 07T8, second assertion, for the flat map `A → A_f`.
(blueprint: lem-weil-pbc-annihilator-localization-finite)

Proof (the node's direct fraction argument):
1. Every `a` in `Ann_A(M)` kills each fraction `m/f^e`, since its product is `am/f^e = 0`.
   Thus the ideal extended along `A → A_f` is contained in `Ann_{A_f}(M_f)`.
   This uses def-weil-ring-localization-away and def-weil-pbc-module-localization-away.
2. Choose finite generators `m_1, …, m_r` of `M` (def-weil-finitely-generated-module).
   An element kills `M` exactly when it kills every generator. The `m_k/1` generate `M_f`,
   since `m/f^e = (1/f^e)(m/1)` and localization is linear, so the same criterion holds there
   (def-weil-pbc-module-localization-away).
3. Write an element of `Ann_{A_f}(M_f)` as `a/f^e`. For each generator its product is zero,
   so the localization equality criterion gives `f^{n_k} a m_k = 0` for some `n_k`.
   Take the maximum `n` of these finitely many exponents, or `n = 0` for no generators.
   Then `f^n a` kills all generators and hence `M`, while
   `a/f^e = (1/f^{n+e})(f^n a/1)` belongs to the extended annihilator ideal.
   This uses def-weil-ring-localization-away and def-weil-pbc-module-localization-away.
4. The two ideal inclusions give the asserted equality. -/
theorem annihilator_localization_away_of_finite
    (A : Type u) [CommRing A] (f : A) (M : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.annihilator (Localization.Away f) (LocalizedModule.Away f M) =
      Ideal.map (algebraMap A (Localization.Away f)) (Module.annihilator A M) := by
  sorry

end Module
