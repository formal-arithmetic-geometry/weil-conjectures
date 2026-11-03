/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification

/-! # Admissibility of the concrete smooth-purity coefficients

Source: the coefficient cases of sk-cor-trace, proof steps 1--6.
(blueprint: lem-pd-transport-coefficient-admissible-for).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Each concrete coefficient is in the fixed-prime admissible family, for
any geometric finite-field datum with the same coefficient prime.
Source: sk-cor-trace, coefficient cases (blueprint: lem-pd-transport-coefficient-admissible-for).
Proof: finite, integral-extension, rational-extension and closure presentations
are the corresponding disjuncts by identity ring-object isomorphisms. For Z_ell
and Q_ell use the canonical isometric identifications with the integer ring and
field of the bottom finite intermediate extension, respectively. -/
theorem Coefficient.admissibleFor {ell : ℕ} [Fact ell.Prime]
    (c : Coefficient ell) (D : WeilConjectures.FiniteFieldDatum.{v})
    (a : D.CoefficientDatum) (ha : a.l = ell) :
    CondensedRing.IsAdmissibleCoefficientFor a (Mon.mk (c.obj.{u} ell)) := by
  subst ell
  cases c with
  | finite A fin n h =>
      let : TopologicalSpace A := ⊥
      let : DiscreteTopology A := discreteTopology_bot A
      exact Or.inl ⟨A, inferInstance, fin, inferInstance, inferInstance, inferInstance,
        ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), h⟩, ⟨Iso.refl _⟩⟩
  | integral E => exact Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)
  | rational E => exact Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))
  | closure => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  | integers =>
      obtain ⟨_, _, _, _, _, _, _, _, _, zIso, _⟩ :=
        Profinite.base_coefficient_condensed_identification.{u} a.l
      exact Or.inr (Or.inl ⟨⟨⊥, inferInstance⟩, ⟨zIso⟩⟩)
  | rationals =>
      obtain ⟨_, _, _, _, _, _, _, _, qIso, _, _⟩ :=
        Profinite.base_coefficient_condensed_identification.{u} a.l
      exact Or.inr (Or.inr (Or.inl ⟨⟨⊥, inferInstance⟩, ⟨qIso⟩⟩))

end AlgebraicGeometry.ProEtale.PurityTransport
