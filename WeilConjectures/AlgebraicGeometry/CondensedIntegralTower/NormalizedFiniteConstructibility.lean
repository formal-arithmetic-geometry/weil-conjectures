/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedAdjunctionCoordinates
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Finite constructibility in the normalized tower adjunction
Source: sk-lem-sp-tower-equivalence, Restriction paragraph.
(blueprint: lem-sp-normalized-finite-constructibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Integral reduction has uniformly constructible normalized finite levels;
the first uniformizer reduction of an effective normalized tower limit is constructible.
Source: sk-lem-sp-tower-equivalence.proof.md, Restriction paragraph
(blueprint: lem-sp-normalized-finite-constructibility).

Proof: the integral-heart reduction theorem supplies normalization and common
cohomological and Tor bounds. Uniqueness of universal derived scalar extension
identifies these reductions with D.red, preserving the ordinary quotient generators
and their derived transitions. This proves forward preservation.
For a normalized constructible tower C, the supplied ambient counit identifies
finiteReduction_m(Rlim C) with C_m by D.levels. The uniformizer quotient is a
quotient of the first ell-power quotient, since ell is a unit times a positive
uniformizer power. Derived scalar associativity identifies its reduction of
Rlim C with the uniformizer reduction of C_0. Constructibility and finite Tor
amplitude at that finite level give bounded constructibility after this scalar
extension. Use the finite scalar local models: on each constructible stratum,
base change the bounded finite projective quotient-coefficient complex.
This retains its bound and finite constant cohomology models. These identifications
are by the actual scalar maps, including for ramified E. No assertion about
integral constructibility or completeness is made here. -/
theorem normalized_finite_constructibility (D : Model l E T) (adj : D.red ⊣ D.rlim)
    (hε : ∀ C : DerivedTowers l E T,
      (∀ (m n : ℕ) (h : m ≤ n), IsIso ((D.reduction h).app C)) →
        IsIso (adj.counit.app C))
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k) (hl : IsUnit (l : k))
    (a : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (hs : IsSeparated a) (hf : LocallyOfFiniteType a) (hq : QuasiCompact a) :
    (∀ M : Dbc l E T, Normalized l E T D (D.red.obj M.obj)) ∧
    (∀ C : NormalizedTowers l E T D,
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) T
        ((AdicCompletion.derivedReduction l E T 0).obj (D.rlim.obj C.obj))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
