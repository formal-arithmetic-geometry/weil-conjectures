/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.SimpleModule.Basic
import WeilConjectures.RingTheory.SimpleFiltration

/-!
# Restriction of scalars length for a semilocal algebra

Source: Stacks Project, Algebra, Tag 02M0 (blueprint: lem-exc-semilocal-restriction-length).
-/

@[expose] public section

universe u v w

open scoped BigOperators
open Ideal Module Localization

/-- Restriction of scalars from a semilocal algebra has residue-degree-weighted length.

Source: Stacks Project, Algebra, Tag 02M0 (`lemma-pushdown-module`)
(blueprint: lem-exc-semilocal-restriction-length).

Proof:
1. Apply `lem-weil-pbc-finite-length-module-simple-filtration` to choose a finite strict
   filtration of `M` by `B`-submodules with simple successive quotients. For `M = 0`,
   use the empty filtration.
2. A nonzero element of each simple quotient generates it. Its annihilator is a maximal
   ideal `q`: if `b` is outside the annihilator, simplicity gives `c` with `cb` acting
   as the identity on the generator. Thus the quotient is isomorphic to `B/q`.
3. Contraction to the maximal ideal of `A` makes `B/q` a vector space over `A/𝔪`.
   A finite basis gives a flag with successive factors `A/𝔪`. The latter has length one,
   since any nonzero vector generates it as an `A`-module.
4. By `lem-weil-pbc-length-additive-short-exact`, the flag gives `A`-length equal to
   the residue degree. Restriction of scalars preserves each short exact sequence in
   the original filtration. Repeated length additivity gives finite `A`-length of `M`,
   equal to the sum of the residue degrees of its simple factors.
5. Localize a factor `B/q'` at `q`. If `q' ≠ q`, an element of `q'` outside `q`
   annihilates the factor and becomes a unit, so the localization is zero. If `q' = q`,
   sending `z/s` to `z` divided by the nonzero residue of `s` identifies its localization
   with `B/q`, which has length one over `B_q` because `B_q → B/q` is surjective.
6. By `lem-weil-pbc-localization-module-exact`, localization preserves the filtration's
   short exact sequences, including zero endpoints. Apply
   `lem-weil-pbc-length-additive-short-exact` over `B_q`: its localized length counts
   exactly the factors supported at `q`. Zero factors need no strict filtration step.
7. Regroup the finite sum of residue degrees by the maximal ideals of `B`. This gives
   the weighted localization sum. For the zero ring `B`, its unital modules are zero,
   and the empty maximal spectrum gives the same zero equality.

The canonical residue fields used here agree with the quotient fields at maximal ideals
via `Ideal.bijective_algebraMap_quotient_residueField`; their scalar action is explicitly
induced by `Ideal.ResidueField.map`, never by an independently chosen field action. -/
theorem semilocal_restriction_length
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsLocalRing A]
    [Algebra A B] (X : Finset (MaximalSpectrum B))
    (hX : ∀ q : MaximalSpectrum B, q ∈ X)
    (hcon : ∀ q : MaximalSpectrum B,
      q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (hdeg : ∀ q : MaximalSpectrum B, q ∈ X →
      @Module.Finite (IsLocalRing.maximalIdeal A).ResidueField q.asIdeal.ResidueField _ _
        (Module.compHom q.asIdeal.ResidueField
          (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal
            (algebraMap A B) (hcon q).symm)))
    (M : Type w) [AddCommGroup M] [Module B M]
    (hM : IsFiniteLength B M) :
    @IsFiniteLength A _ M _
        (@Module.compHom B A M _ _ (inferInstance : Module B M) _ (algebraMap A B)) ∧
      @Module.length A M _ _
        (@Module.compHom B A M _ _ (inferInstance : Module B M) _ (algebraMap A B)) =
        ∑ q ∈ X,
          @Module.finrank (IsLocalRing.maximalIdeal A).ResidueField q.asIdeal.ResidueField
            _ _ (Module.compHom q.asIdeal.ResidueField
              (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal
                (algebraMap A B) (hcon q).symm)) *
            Module.length (Localization.AtPrime q.asIdeal)
              (LocalizedModule q.asIdeal.primeCompl M) := by
  sorry

end
