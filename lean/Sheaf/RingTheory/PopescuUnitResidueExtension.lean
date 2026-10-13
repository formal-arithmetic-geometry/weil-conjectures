/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Defs

import Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian
import Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Sheaf.RingTheory.HenselianOfNilMaximalIdeal
import Sheaf.RingTheory.HenselianFiniteEtaleEquivalence
import Sheaf.RingTheory.HenselianEtaleRetraction

/-!
# Residue-field geometry of an admissible unit enlargement

Source: Stacks Project, Tags 07FH and 07FI.
(blueprint: lem-weil-pbc-popescu-unit-residue-extension).
-/

@[expose] public section

set_option autoImplicit false
universe u v

namespace Algebra

/-- The geometric enlargement, without any input or output differential basis.
Source: Stacks Project, smoothing.tex, Tags 07FH and 07FI; steps 1–4 and 6–8 of
lem-weil-pbc-popescu-unscaled-unit-basis.
(blueprint: lem-weil-pbc-popescu-unit-residue-extension).

Proof: Put B = Λ_q/(qΛ_q)^n and x = π(s). It is Artinian local and x is a unit.
Admissibility identifies the maximal ideal of A₀ with the contraction of that of B,
so its residue field F₀ embeds into K = B/m_B. Let α be the residue of x.
If α is transcendental, localize A₀[T] at m₀[T] and evaluate T at x. Reduction is
F₀[T] → K, which is injective, and localization has residue F₀(α). Its maximal
ideal is the extension of the nilpotent m₀; it is Noetherian, hence Artinian.
The fibre flatness criterion makes evaluation flat, since B is flat over A₀ and
its closed fibre is a vector space over F₀(α). A flat local map is faithfully flat,
hence injective. Its image A is Artinian local, flatly included in B, and has
m_A B = m_B. Its residue is essentially finite type over k, so the Artinian
residue criterion makes A essentially finite type. Take m = 1, y₀ = x, Q = 1,
and z = x⁻¹; the error is zero.
If α is algebraic, choose Q = p^e ≥ 1 with β = α^Q separable over F₀. Nilpotent
maximal ideals make A₀ and B henselian. Lift F₀(β)/F₀ to a finite étale local
A₀-algebra D and use the henselian étale retraction of D ⊗[A₀] B at the prime
specified by F₀(β) → K to map D into B. The same fibre flatness argument makes
this map injective and its image admissible. Its residue extension is finite
separable, hence formally étale. Take m = 0. Lift β⁻¹ to a unit z of A; the
residue of z x^Q - 1 is zero, so this error is nilpotent. In both cases the
residue algebra and scalar tower come from inclusion A₀ → A; the displayed
compatibility holds by the universal property of the residue quotient.
No differential basis is used in constructing A. -/
theorem exists_popescu_unit_residue_extension
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (q : Ideal Λ) [q.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (A₀ : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) [IsLocalRing A₀]
    (hA₀ : A₀.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))))
    (s : Λ) (hs : s ∉ q) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      ∃ hle : A₀ ≤ A,
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      ∃ (Q : ℕ) (_ : 1 ≤ Q) (z : Aˣ),
        IsNilpotent (((z : A) : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) *
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
            (algebraMap Λ (Localization.AtPrime q) s)) ^ Q - 1) ∧
        ∃ (m : ℕ) (y : Fin m → A),
          (∀ j, (y j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) s)) ∧
          ∃ (alg : Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A)),
            letI := alg
            IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A) ∧
            (∀ a : A₀, algebraMap (IsLocalRing.ResidueField A₀)
              (IsLocalRing.ResidueField A) (IsLocalRing.residue A₀ a) =
                IsLocalRing.residue A (Subalgebra.inclusion hle a)) ∧
            ((m = 0 ∧ Algebra.FormallyEtale (IsLocalRing.ResidueField A₀)
                (IsLocalRing.ResidueField A)) ∨
              (m = 1 ∧
                (∀ j, Transcendental (IsLocalRing.ResidueField A₀)
                  (IsLocalRing.residue A (y j))) ∧
                IntermediateField.adjoin (IsLocalRing.ResidueField A₀)
                  (Set.range (fun j ↦ IsLocalRing.residue A (y j))) = ⊤)) := by sorry

end Algebra
