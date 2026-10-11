/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.MeromorphicModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Topology.GDelta.Basic

/-!
# The denominator ideal of a regular meromorphic section

Source: Stacks Project, Divisors, Tag 02P0, Lemma 31.24.9
(blueprint: lem-sc-hilbert-denominator-ideal-nowhere-dense).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Source: Stacks Project, Tag 02P0
(blueprint: lem-sc-hilbert-denominator-ideal-nowhere-dense).

1. Locally trivialize L on an affine open. Sheafification gives a local fraction a/b.
Regularity makes a a non-zero-divisor: a scalar annihilating a annihilates s, hence vanishes.
The injection O_X → K_X identifies the denominator ideal with {y | y(a/b) ∈ A}.
2. Localization of that ideal at f gives precisely the denominators of a/b over A_f:
clear a power of f for one inclusion; the reverse inclusion follows by localization.
This proves quasi-coherence.
3. Both maps out of the ideal are injective: the first is inclusion and the second is
multiplication by the regular section. Locally b lies in I and s(b) = a. Consequently the
cokernels are supported inside V(b) and V(a). Non-zero-divisors give dense principal opens
(lem-pc-principal-open-dense-of-nonzerodivisor), so these supports have nowhere-dense
closures. The local assertions glue.

The section s is represented by its O_X-linear map from O_X. The induced map from K_X
is `meromorphicSectionMap`; its monomorphism is exactly regularity. The ideal is the pullback
of L → K_X(L) along s; its projections are the maps denoted 1 and s in the source.
Membership y(a/b) ∈ A is stated in the total ring of fractions
`Localization (nonZeroDivisors A)`, as in lem-sc-hilbert-affine-denominator-module.
Support containment is expressed by vanishing cokernel stalks outside a closed
nowhere-dense set. -/
theorem meromorphic_denominator_ideal_nowhere_dense (X : Scheme.{v}) (L : X.Modules)
    [L.IsInvertible]
    (s : unit X ⟶ meromorphicModule X L)
    (hs : Mono (meromorphicSectionMap X L s)) :
    let I : X.Modules := CategoryTheory.Limits.pullback s (toMeromorphicModule X L)
    let i : I ⟶ unit X := CategoryTheory.Limits.pullback.fst s (toMeromorphicModule X L)
    let j : I ⟶ L := CategoryTheory.Limits.pullback.snd s (toMeromorphicModule X L)
    (∀ (V : X.Opens) (f : Γ(X, V)),
      (∃ t : Γ(I, V), Hom.app i V t = f) ↔
        ∃ t : Γ(L, V), Hom.app (toMeromorphicModule X L) V t = Hom.app s V f) ∧
    (∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      ∃ (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
        (a : Γ(X, U)) (b : meromorphicDenominators X U),
        a ∈ nonZeroDivisors Γ(X, U) ∧ ∃ hb : b.val ∈ nonZeroDivisors Γ(X, U),
        meromorphicFraction X L U
          (LocalizedModule.mk ((sectionsLinearEquivOfOverIsoUnit e le_rfl).symm a) b) =
          Hom.app s U (1 : Γ(X, U)) ∧
        ∀ y : Γ(X, U),
          (∃ t : Γ(I, U), Hom.app i U t = y) ↔
            ∃ c : Γ(X, U),
              algebraMap Γ(X, U) (Localization (nonZeroDivisors Γ(X, U))) c =
                IsLocalization.mk' (Localization (nonZeroDivisors Γ(X, U))) a
                    ⟨b.val, hb⟩ *
                  algebraMap Γ(X, U) (Localization (nonZeroDivisors Γ(X, U))) y) ∧
    SheafOfModules.IsQuasicoherent I ∧ Mono i ∧ Mono j ∧
    (∃ Z : Set X, IsClosed Z ∧ IsNowhereDense Z ∧
      ∀ x : X, x ∉ Z → Subsingleton ((presheaf (cokernel i : X.Modules)).stalk x)) ∧
    (∃ Z : Set X, IsClosed Z ∧ IsNowhereDense Z ∧
      ∀ x : X, x ∉ Z → Subsingleton ((presheaf (cokernel j : X.Modules)).stalk x)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
