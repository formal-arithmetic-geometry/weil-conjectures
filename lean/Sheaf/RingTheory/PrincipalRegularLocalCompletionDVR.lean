module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Completion at a principal regular maximal ideal

Source: Stacks Project, Algebra, Tag 0328 (lemma-cohen-rings-exist), completion step,
with an arbitrary regular generator in place of the prime number; Tags 05GG, 05GI,
and 00PD supply completion, locality, and the DVR criterion.
(blueprint: lem-sfb-principal-regular-local-completion-dvr).
-/

@[expose] public section

universe u

namespace AdicCompletion

/-- Completion of a nonzero local ring at its regular principal maximal ideal is a
complete DVR. Its uniformizer is the image of the given generator, and the quotient
isomorphism is induced by the first-coordinate projection and respects the map from
`S`. No Noetherianity, domain, or separatedness of `S` is assumed.

Source: Stacks Project, Algebra, Tag 0328 (lemma-cohen-rings-exist), completion step
with an arbitrary regular generator; Tags 05GG, 05GI, and 00PD.
(blueprint: lem-sfb-principal-regular-local-completion-dvr).

Proof:
1. Put `I = (t)`. This ideal is finitely generated and is the maximal ideal of `S`,
   so `S/I` is a field. By lem-weil-pbc-adic-completion-mod-ideal (Tag 05GG), the
   first-coordinate map from `D = AdicCompletion I S` to `S/I` is surjective with
   kernel `ID = (image t)`. It induces the quotient isomorphism compatibly with
   `S → D`, and `D` is `ID`-adically complete.
2. The ideal `ID` is maximal since the quotient is a field. By
   lem-weil-pbc-adic-complete-jacobson-radical (Tag 05GI), it lies in every maximal
   ideal. Thus `D` is local with maximal ideal `ID`, and the completeness in step 1
   is completeness for this maximal ideal.
3. Injectivity of multiplication by `t` implies `t ≠ 0`. Since `t` generates a
   proper ideal, it is not a unit. If `t` belonged to `(t²)`, cancellation would
   make it a unit. Its class in `S/(t²)` is therefore nonzero, so its image in `D`
   is nonzero.
4. Multiplication by the image of `t` on `D` is injective: if its product with `x`
   vanishes, lift the `(n+1)`st component of `x` to `a` in `S`. Then `ta` belongs
   to `(t^(n+1))`. Cancel `t` in `S` to see that `a` belongs to `(t^n)`, so the nth
   component of `x` vanishes. This holds for every `n`, hence `x = 0`.
5. Completeness includes separatedness. A nonzero `x` therefore lies in a largest
   power `r` of the maximal ideal. Write `x = (image t)^r * y`. If `y` were in the
   maximal ideal then `x` would lie in the next power. Thus `y` is a unit by
   locality. This is the unit-times-uniformizer-power argument of Tag 00PD.
6. The quotient field in step 1 makes `D` nontrivial. Factor two nonzero elements
   as in step 5. Cancellation of powers of the image of `t` using step 4, and of
   their unit factors, shows their product is nonzero. Thus `D` is a domain. The
   nonzero image of `t` in its maximal ideal shows that it is not a field.
7. A nonzero ideal contains an element with least exponent in step 5. Every other
   element is divisible by this element, so it generates the ideal. The zero
   ideal is principal as well. Hence `D` is a local principal ideal domain that
   is not a field, exactly def-sc-discrete-valuation-ring. Step 1 supplies the
   asserted quotient isomorphism and its compatibility. -/
theorem principalRegularLocalCompletion_dvr
    (S : Type u) [CommRing S] [IsLocalRing S]
    (t : S) (hMax : IsLocalRing.maximalIdeal S = Ideal.span {t})
    (hRegular : Function.Injective (fun x : S => t * x)) :
    ∃ (_ : IsDomain (AdicCompletion (Ideal.span {t}) S))
      (_ : IsDiscreteValuationRing (AdicCompletion (Ideal.span {t}) S)),
      IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion (Ideal.span {t}) S))
        (AdicCompletion (Ideal.span {t}) S) ∧
      IsLocalRing.maximalIdeal (AdicCompletion (Ideal.span {t}) S) =
        Ideal.span {algebraMap S (AdicCompletion (Ideal.span {t}) S) t} ∧
      algebraMap S (AdicCompletion (Ideal.span {t}) S) t ≠ 0 ∧
      ∃ e : (AdicCompletion (Ideal.span {t}) S ⧸
          Ideal.span {algebraMap S (AdicCompletion (Ideal.span {t}) S) t}) ≃+*
          (S ⧸ Ideal.span {t}),
        (∀ x : AdicCompletion (Ideal.span {t}) S,
          e (Ideal.Quotient.mk
            (Ideal.span {algebraMap S (AdicCompletion (Ideal.span {t}) S) t}) x) =
              AdicCompletion.evalOneₐ (Ideal.span {t}) x) ∧
        (∀ s : S,
          e (Ideal.Quotient.mk
            (Ideal.span {algebraMap S (AdicCompletion (Ideal.span {t}) S) t})
            (algebraMap S (AdicCompletion (Ideal.span {t}) S) s)) =
              Ideal.Quotient.mk (Ideal.span {t}) s) := by
  sorry

end AdicCompletion
