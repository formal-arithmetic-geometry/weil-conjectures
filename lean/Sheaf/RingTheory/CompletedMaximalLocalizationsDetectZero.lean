module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Stability
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.RingTheory.Ideal.Maximal

/-! # Completed maximal localizations detect zero derived objects

Source: Stacks Project, algebra.tex, Tags 00MC and 00HN, with Tags 0316,
05GG and 05GI for completion properties, and derived.tex, Tag 015F.
(blueprint: lem-trf-completed-maximal-localizations-detect-zero)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Completed maximal localizations are complete local flat tests for zero objects
in the unbounded ordinary-module derived category. Each displayed completion is
at the extended ideal `m Rₘ`, and its algebra maps are the canonical maps.
Localness together with maximality identifies that extended ideal as the unique
maximal ideal, without choosing a second local-ring structure.

Source: Stacks Project, algebra.tex, Tags 00MC, 00HN, 0316, 05GG and 05GI;
derived.tex, Tag 015F.
(blueprint: lem-trf-completed-maximal-localizations-detect-zero)

Proof:
1. A maximal ideal is prime. Localization at its complement is local with maximal
   ideal `m Rₘ`; localization preserves Noetherianity and is flat (localization-at-prime,
   localization-noetherian and localization-flat nodes).
2. Completion is Noetherian (adic-completion-noetherian). The ideal `m Rₘ` is finitely
   generated, so adic-completion-mod-ideal gives completeness for its extension.
   Local-completion-local-ring identifies this extension as the maximal ideal and
   its residue field with that of `Rₘ`. Thus the completion is nonzero.
3. Local-completion-faithfully-flat makes `Rₘ → Bₘ` faithfully flat. Flat transitivity
   (lem-pc-module-flat-transitive) gives flatness of `R → Bₘ`.
4. Flat tensor is exact (flat-tensor-exact). Exact-functor-derived-factorization and
   exact-functor-derived-functor identify its termwise descent with the derived scalar
   extension of lem-pur-derived-change-of-rings. Exact-functor-complex-cohomology gives
   `H^q(K ⊗ᴸ Bₘ) ≅ H^q(K) ⊗ Bₘ` for every integer, with no boundedness condition.
5. Zero objects extend to zero. Conversely, if every extended object is zero, tensor
   associativity identifies `(H^q(K) ⊗ Rₘ) ⊗ Bₘ` with `H^q(K) ⊗ Bₘ = 0`.
   Faithful flatness and lem-sc-faithfully-flat-tensor-zero give `H^q(K) ⊗ Rₘ = 0`.
6. Identify this tensor product with the localized module. A nonzero element has a
   proper annihilator contained in a maximal ideal (proper-ideal-contained-in-maximal).
   Its localized image cannot vanish there: vanishing would give an annihilator
   outside that maximal ideal. Thus every cohomology module vanishes (Tag 00HN).
7. An acyclic complex becomes zero in the derived localization
   (def-weil-abstract-derived-category). For the zero ring every unital module and
   hence every derived object is zero; the family of maximal ideals is empty. -/
theorem completedMaximalLocalizations_detect_zero (R : Type u)
    [CommRing R] [IsNoetherianRing R] :
    (∀ (m : Ideal R) [m.IsMaximal],
      IsNoetherianRing (Localization.AtPrime m) ∧
      IsLocalRing (Localization.AtPrime m) ∧
      (m.map (algebraMap R (Localization.AtPrime m))).IsMaximal ∧
      Nontrivial (AdicCompletion (m.map (algebraMap R (Localization.AtPrime m)))
        (Localization.AtPrime m)) ∧
      IsNoetherianRing (AdicCompletion (m.map (algebraMap R (Localization.AtPrime m)))
        (Localization.AtPrime m)) ∧
      IsLocalRing (AdicCompletion (m.map (algebraMap R (Localization.AtPrime m)))
        (Localization.AtPrime m)) ∧
      ((m.map (algebraMap R (Localization.AtPrime m))).map
        (algebraMap (Localization.AtPrime m)
          (AdicCompletion (m.map (algebraMap R (Localization.AtPrime m)))
            (Localization.AtPrime m)))).IsMaximal ∧
      IsAdicComplete ((m.map (algebraMap R (Localization.AtPrime m))).map
        (algebraMap (Localization.AtPrime m)
          (AdicCompletion (m.map (algebraMap R (Localization.AtPrime m)))
            (Localization.AtPrime m))))
        (AdicCompletion (m.map (algebraMap R (Localization.AtPrime m)))
          (Localization.AtPrime m)) ∧
      Module.FaithfullyFlat (Localization.AtPrime m)
        (AdicCompletion (m.map (algebraMap R (Localization.AtPrime m)))
          (Localization.AtPrime m)) ∧
      Module.Flat R (Localization.AtPrime m) ∧
      Module.Flat R (AdicCompletion (m.map (algebraMap R (Localization.AtPrime m)))
        (Localization.AtPrime m))) ∧
    (∀ K : DerivedCategory (ModuleCat.{u} R),
      IsZero K ↔ ∀ (m : Ideal R) [m.IsMaximal],
        IsZero ((ordinaryDerivedExtendScalars
          (algebraMap R (AdicCompletion (m.map (algebraMap R (Localization.AtPrime m)))
            (Localization.AtPrime m)))).obj K)) := by
  sorry

end ModuleCat
