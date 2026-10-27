/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.FlatUnderRegular
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Compactification.BoundarySeparationData
import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal
import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-!
# Good neighborhoods detected by a principal completion

Source: Temkin, Desingularization of quasi-excellent schemes in characteristic zero,
Corollary 3.1.5(ii), its reducedness comparison (printed p.18), and the shrinking in
Theorem 3.4.1 (printed p.22). The parameter-torsion assertion uses the finite kernel of
multiplication by the parameter (blueprint: lem-per-principal-completion-good-neighborhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A quasi-excellent ring with reduced, parameter-torsion-free principal completion and
regular punctured completion has a principal neighborhood of its closed fibre with these
properties. The equivalence of completions is specified on every positive-power quotient
by the localization map; hence it is the canonical completion map and preserves the image
of every element of `C`, in particular the distinguished generator `t`.

Source: Temkin, Corollary 3.1.5(ii), its reducedness comparison (printed p.18), and the
shrinking in the proof of Theorem 3.4.1 (printed p.22)
(blueprint: lem-per-principal-completion-good-neighborhood).

Proof plan:
1. Quasi-excellence gives Noetherianity and J-2, so the singular locus of `Spec C` is
   `V(I)` for an ideal `I`. Completion is Noetherian and flat by
   [lem-weil-pbc-adic-completion-noetherian] and [lem-weil-pbc-noetherian-completion-flat].
2. Let `N` be the nilradical and `T` the kernel of multiplication by `t`. Both are finite.
   Exactness and the tensor description of completion show their completions vanish:
   reducedness kills the completed image of `N`, and injectivity of `t` kills that of `T`.
   Surjective first projections give `N/tN = T/tT = 0`. Nakayama in its `1+(t)` form
   supplies `hN,hT` annihilating these ideals, using
   [lem-weil-pbc-completion-exact-finite-modules],
   [lem-weil-pbc-completion-finite-module-tensor],
   [lem-weil-pbc-module-completion-complete], and
   [lem-weil-pbc-nakayama-one-plus-ideal-annihilator].
3. Saturate `I` by powers of `t`, obtaining `J`. Multiplication by `t` on `C/J` is
   injective. Exactness identifies its completion with `R = B/JB`, on which `t` is
   still injective, by the same exactness and tensor-description nodes.
4. A prime of `R` avoiding `t` would contract to a singular prime of `C`, but its
   local ring in `B` is regular by punctured regularity. The induced flat local map
   contradicts [lem-weil-pbc-flat-local-ring-maps] and [lem-weil-pbc-flat-under-regular].
5. Thus every prime of `R` contains `t`. On the quasi-compact affine `Spec R`, the
   finite-type principal ideal sheaf `(t)` has full vanishing set and is nilpotent by
   [lemma-nagata-finite-type-nil-ideal-nilpotent], using
   [lem-weil-pbc-affine-scheme-qcqs],
   [lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal], and [pqf-def-coherent].
   Injectivity of `t` forces `R = 0`. The first completion projection then gives
   `J+(t)=C`, so some `hJ` in `1+(t)` satisfies `t^n*hJ ∈ I`.
6. Put `g=hN*hT*hJ`. The fraction formulas show `C_g` is reduced and `t` is injective
   on it. Inverting `t` also makes `t^n*hJ` a unit, so all remaining primes avoid
   `V(I)` and have regular local rings. Noetherianity follows from
   [lem-weil-pbc-localization-noetherian], giving regularity by [def-weil-regular-scheme].
7. Write `g=1+t*c`. Modulo `t^r`, the geometric sum of `(-t*c)^i`, for `i<r`, inverts
   `g`. The resulting canonical quotient equivalences commute with transitions, since
   they extend the same localization map. Applying them coordinatewise gives the
   displayed completion equivalence and its projection identities. The quotient
   description of [lem-weil-pbc-adic-completion-mod-power] also identifies the quotients
   of the completions themselves. -/
theorem exists_goodNeighborhood_of_principalCompletion
    (C : Type u) [CommRing C] (hC : IsQuasiExcellent C) (t : C)
    (hred : IsReduced (AdicCompletion (Ideal.span {t}) C))
    (ht : Function.Injective (fun b : AdicCompletion (Ideal.span {t}) C ↦
      algebraMap C (AdicCompletion (Ideal.span {t}) C) t * b))
    (hreg : IsRegularRing (Localization.Away
      (algebraMap C (AdicCompletion (Ideal.span {t}) C) t))) :
    ∃ g : C, (∃ c : C, g = 1 + t * c) ∧
      IsReduced (Localization.Away g) ∧
      Function.Injective (fun a : Localization.Away g ↦
        algebraMap C (Localization.Away g) t * a) ∧
      IsRegularRing (Localization.Away (algebraMap C (Localization.Away g) t)) ∧
      ∃ E : AdicCompletion (Ideal.span {t}) C ≃+*
          AdicCompletion (Ideal.span {algebraMap C (Localization.Away g) t})
            (Localization.Away g),
        (∀ c : C, E (algebraMap C (AdicCompletion (Ideal.span {t}) C) c) =
          algebraMap (Localization.Away g)
            (AdicCompletion (Ideal.span {algebraMap C (Localization.Away g) t})
              (Localization.Away g)) (algebraMap C (Localization.Away g) c)) ∧
        ∀ n : ℕ, 0 < n →
          ∃ e : (C ⧸ (Ideal.span {t}) ^ n) ≃+*
              ((Localization.Away g) ⧸
                (Ideal.span {algebraMap C (Localization.Away g) t}) ^ n),
            (∀ c : C, e (Ideal.Quotient.mk ((Ideal.span {t}) ^ n) c) =
              Ideal.Quotient.mk
                ((Ideal.span {algebraMap C (Localization.Away g) t}) ^ n)
                (algebraMap C (Localization.Away g) c)) ∧
            ∀ b : AdicCompletion (Ideal.span {t}) C,
              AdicCompletion.evalₐ
                (Ideal.span {algebraMap C (Localization.Away g) t}) n (E b) =
                  e (AdicCompletion.evalₐ (Ideal.span {t}) n b) := by
  sorry
