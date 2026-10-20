/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data
import Sheaf.AlgebraicGeometry.OrdinaryFiniteClassInjectivity
import Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The normalized projective-line datum is unique

Source: blueprint projective-line adjunction and vector integration, normalized
Kummer class, decomposition components and counit.
(blueprint: lem-amb-ordinary-finite-p1-datum-uniqueness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Every field of the projective-line datum is fixed by its normalization.
Source: blueprint projective-line decomposition and adjunction; vector integration.
(blueprint: lem-amb-ordinary-finite-p1-datum-uniqueness).

Proof: the free-constant-coefficient Ext comparison makes the Chern arrow unique
from its Kummer class. The two prescribed components then identify the decomposition.
The reordered proper projection map is invertible, so the counit normalization
identifies each component of the two counits. An adjunction is determined by its
counit. Function extensionality, isomorphism extensionality and proof irrelevance
identify all fields of the datum. No connectedness or nonzero-coefficient hypothesis
is used, and rank plays no role. -/
theorem ordinaryFiniteP1Datum_unique (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (D D' : OrdinaryFiniteP1Datum A N hA t S hS) : D = D' := by
  let : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  let : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  let : IsProper (ProjectiveLine S ↘ S) :=
    ProjectiveSpace.instIsProper (ULift (Fin 2)) S
  have hc : D.chern = D'.chern := by
    apply ordinaryFiniteClass_injective A (ProjectiveLine S)
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2
    exact D.chern_spec.trans D'.chern_spec.symm
  have hb : D.decomposition = D'.decomposition := by
    apply Iso.ext
    rw [D.decomposition_hom, D'.decomposition_hom, hc]
  have ha : D.adjunction = D'.adjunction := by
    apply Adjunction.ext_counit
    ext K
    let : IsIso (ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K) :=
      isIso_proper_projection_formula_reordered A (ProjectiveLine S ↘ S)
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K
    apply (cancel_epi (ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K)).mp
    rw [D.counit_normalization K, D'.counit_normalization K, hb]
  cases D
  cases D'
  cases hc
  cases hb
  cases ha
  rfl

private theorem property_of_unique_parameters
    {I : Sort*} {F : I → Sort*}
    (hI : ∀ i j : I, i = j) (hF : ∀ i (a b : F i), a = b)
    (P : ∀ i, F i → Prop) (hP : ∃ i a, P i a) (i : I) (a : F i) : P i a := by
  obtain ⟨j, b, hb⟩ := hP
  obtain rfl := hI j i
  obtain rfl := hF j b a
  exact hb

/-- The normalization already forces base change, without assuming it as extra data.
Source: blueprint projective-line adjunction, base-change clause.
(blueprint: lem-amb-ordinary-finite-p1-datum-uniqueness).

Proof: choose the normalized family with base change supplied by the existing
projective-line adjunction theorem. Tate-transport uniqueness identifies its
transport with the specified one. Pointwise datum uniqueness identifies its
family with the specified family. Transport the proved base-change equations
through these equalities. This chooses no new mathematical object. -/
theorem ordinaryFiniteP1BaseChange_of_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) : OrdinaryFiniteP1BaseChange A N hA t D := by
  exact property_of_unique_parameters
    (F := fun t ↦ ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (N : Γ(T, ⊤))), OrdinaryFiniteP1Datum A N hA t T hT)
    (ordinaryFiniteTwistTransport_unique A N hA)
    (fun t D D' ↦ by
      funext T inst hT
      exact ordinaryFiniteP1Datum_unique A N hA t T hT (D T hT) (D' T hT))
    (fun t D ↦ OrdinaryFiniteP1BaseChange A N hA t D)
    (exists_ordinaryFiniteP1Adjunction N hN A hA) t D

end AlgebraicGeometry.Etale
