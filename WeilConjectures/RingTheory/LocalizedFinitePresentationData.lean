/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.FinitePresentation

import WeilConjectures.RingTheory.FinitelyPresentedAlgebraModuleGenericFreeness

/-!
# Finite presentation data after generic localization

The finite exact sequence underlying the generic finite-presentation argument is isolated here.
Source: Stacks Project, Tag 051T, algebra-lemma-generic-flatness (blueprint:
lem-pur-generic-finite-module-presentation).
-/

@[expose] public section

universe u v w

namespace Module.Finite

/--
After inverting a suitable nonzero element of the base, a finite module over a finite type
algebra admits a finite free presentation.  The finite free presentation is recorded as an
explicit surjection and an exact relation map; this is the concrete relation-column part of the
proof of `exists_finitePresentation_localizedModule_powers`.

The proof is the polynomial-presentation and generic-freeness argument of Stacks Project,
Tag 051T: choose finitely many algebra and module generators, pass to the fraction field of the
base, use Noetherianity there to obtain finitely many relation generators, clear their
coefficients' denominators, and shrink once more using generic freeness.  Localizing the resulting
finite relation presentation gives the displayed exact sequence.

(blueprint: lem-pur-generic-finite-module-presentation-data)
-/
theorem exists_localized_finite_presentation_data
    (R : Type u) (B : Type v) (M : Type w)
    [CommRing R] [IsDomain R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] :
    ∃ (a : R), a ≠ 0 ∧
      ∃ (n m : ℕ)
        (f : (Fin n → Localization.Away (algebraMap R B a)) →ₗ[
          Localization.Away (algebraMap R B a)]
          LocalizedModule.Away (algebraMap R B a) M)
        (g : (Fin m → Localization.Away (algebraMap R B a)) →ₗ[
          Localization.Away (algebraMap R B a)]
          (Fin n → Localization.Away (algebraMap R B a))),
        Function.Surjective f ∧ Function.Exact g f := by
  sorry

end Module.Finite
