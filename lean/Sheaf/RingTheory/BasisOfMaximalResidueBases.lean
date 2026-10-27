/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.OrzechProperty
import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# A prescribed basis from bases in every maximal residue module

Source: Stacks Project, Algebra, Tags 02M9, final proof hint, and 03C1, first proof sentences
(blueprint: lem-a1-basis-of-maximal-residue-bases).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- A prescribed finite family is a basis if it is a basis modulo every maximal ideal
and the module is free of the same rank at every maximal localization.

Source: Stacks Project, Algebra, Tags 02M9, final proof hint, and 03C1, first proof sentences
(blueprint: lem-a1-basis-of-maximal-residue-bases).

Proof:
1. Fix a maximal ideal `q`. Localization identifies the finite coordinate module with
   the coordinate module over `Localization.AtPrime q`, by a common denominator
   [def-weil-pbc-module-localization, def-weil-pbc-localization-at-prime]. The localized
   map sends coordinates to the linear combination of the vectors `n i / 1`.
2. The residue-basis hypothesis implies that these localized vectors generate modulo
   the maximal ideal of the local ring: express a numerator modulo `qP` using the
   prescribed residue basis and divide the resulting expression by its denominator
   [def-weil-pbc-module-localization].
3. The local basis in `hfree` makes the localized module finite. Nakayama's lemma
   makes the localized linear combination map surjective
   [lem-weil-pbc-nakayama-local-generators].
4. A local basis identifies this map with a surjective endomorphism of a finite free
   module. It is bijective by the finite-module endomorphism lemma
   [lem-weil-pbc-finite-module-surjective-endomorphism-bijective].
5. Bijectivity at every maximal localization implies global bijectivity
   [lem-weil-pbc-linear-map-bijective-at-maximal-localizations], which is the prescribed
   basis property [def-weil-pbc-free-module]. The finite sums allow rank zero. Over the
   zero ring every module is zero, so the assertion also holds with no maximal ideals. -/
theorem bijective_linearCombination_of_maximal_residue_bases
    {E : Type u} [CommRing E] {P : Type v} [AddCommGroup P] [Module E P]
    (r : ℕ) (n : Fin r → P)
    (hfree : ∀ (q : Ideal E) [q.IsMaximal],
      Nonempty (Module.Basis (Fin r) (Localization.AtPrime q)
        (LocalizedModule q.primeCompl P)))
    (hres : ∀ (q : Ideal E) [q.IsMaximal],
      ∃ b : Module.Basis (Fin r) (E ⧸ q) (P ⧸ (q • (⊤ : Submodule E P))),
        ∀ i : Fin r, b i = (q • (⊤ : Submodule E P)).mkQ (n i)) :
    Function.Bijective (Fintype.linearCombination E n) := by
  sorry

end Module
