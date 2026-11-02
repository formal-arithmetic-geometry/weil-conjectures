/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernFlagFormula
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernProjectivePolynomialValue
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDerivedRightUnitPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteSingleUnitNaturality
import Mathlib.Algebra.Group.Hom.End
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.Algebra.DirectSum.Basic
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernFlagCoefficientAlgebra
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernClasses
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels
import WeilConjectures.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernLineDivisorAnnihilation

/-! # The single line-subbundle step in the Chern induction

Source: Stacks Project, Tag 0FI5, proposition-chern-class, invertible-submodule paragraph.
(blueprint: lem-pur-chern-line-subbundle-recurrence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- A single invertible subbundle contributes one linear factor to the Chern polynomial.
This statement involves one short exact sequence, not a flag or any induction hypothesis.

Source: Stacks Project, Tag 0FI5, proposition-chern-class and equation-chern-classes;
blueprint localized-top-Chern Step 2 and Step 4 (L4).
(blueprint: lem-pur-chern-line-subbundle-recurrence).

Proof: form the explicit candidate with coefficient zero equal to the unit and
coefficient i+1 equal to c_(i+1)(G) plus x times c_i(G). Above rank n+1 both
summands vanish by the above-rank convention for G and additivity of the tensor
operator. The single-line projective-relation lemma proves the defining relation
for this candidate on every normalized projective realization and for every twist
transport, including rank one. Thus it satisfies IsOrdinaryFiniteChernClasses.
Apply the existing uniqueness theorem for the Chern family of F and evaluate its
family equality at i+1. This uses no flag and no induction hypothesis. -/
theorem ordinaryFiniteChernClass_lineSubbundle (P : PurityFiniteSetting.{u})
    {S : Scheme.{u}} (a : S ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (n : ℕ) (L F G : S.Modules) [L.IsInvertible]
    [F.IsFiniteLocallyFreeOfRank (n + 1)] [G.IsFiniteLocallyFreeOfRank n]
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (hexact : (ShortComplex.mk ι π w).ShortExact) (i : ℕ) :
    P.ordinaryFiniteChernClass a F (n + 1) (i + 1) =
      P.ordinaryFiniteChernClass a G n (i + 1) +
        P.ordinaryFiniteHyperplaneStep S (P.ordinaryFiniteFlagRoot a L inferInstance) i
          (P.ordinaryFiniteChernClass a G n i) := by
  let c := P.lineSubbundleChernCandidate a n L G inferInstance
  have hp : P.IsOrdinaryFiniteChernClasses a F (n + 1) c := by
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => omega
      | succ j =>
        have hG := (P.existsUniqueOrdinaryFiniteChernClasses a G n).exists.choose_spec
        have hj0 : P.ordinaryFiniteChernClass a G n j = 0 := hG.2.1 j (by omega)
        have hj1 : P.ordinaryFiniteChernClass a G n (j + 1) = 0 :=
          hG.2.1 (j + 1) (by omega)
        dsimp only [c, lineSubbundleChernCandidate]
        rw [hj0, hj1, ordinaryFiniteHyperplaneStep_zero, add_zero]
    · intro _ D hD t
      exact lineSubbundleChernCandidate_relation P a n L F G ι π w hexact D hD t
  have hunique := P.existsUniqueOrdinaryFiniteChernClasses a F (n + 1)
  have heq : c = P.ordinaryFiniteChernClasses a F (n + 1) :=
    hunique.unique hp hunique.exists.choose_spec
  exact (congrFun heq (i + 1)).symm

end WeilConjectures.PurityFiniteSetting
