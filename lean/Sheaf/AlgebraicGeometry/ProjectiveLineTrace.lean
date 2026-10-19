/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import Sheaf.AlgebraicGeometry.ProperProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# The ordinary finite-coefficient projective-line trace

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/def-amb-p1-trace.md
(blueprint: def-amb-p1-trace).

All categories are the entire derived categories of ordinary small-etale module sheaves.
The decomposition is characterized by its shifted twisted unit and the scalar Kummer
class of O(1). Its inverse, and hence the trace below, are determined by these maps.

## Main definitions

* `projectiveLineTraceDatum`: the canonical normalized decomposition datum.
* `projectiveLineTrace`: projection onto the second summand after inverse decomposition.
* `projectiveLineTraceEpsilon`: the inverse projection formula followed by tensor trace.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical finite-twist transport furnished by the projective-line theorem.
The roots inclusion and pure-tensor equations characterize this transport, so this
selection does not introduce a choice of orientation or a primitive root.
Source: blueprint def-amb-p1-trace (blueprint: def-amb-p1-trace). -/
def projectiveLineTraceTransport (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    OrdinaryFiniteTwistTransport A N hA :=
  Classical.choose (exists_ordinaryFiniteP1Adjunction N hN A hA)

/-- The normalized decomposition from the recorded ordinary projective-line theorem.
The Chern arrow is fixed by its cohomology realization, the decomposition by its two
components, and the adjunction by its counit. Consequently all data used below are
independent of the witness selected here, up to the equality of the specified arrows.
Source: blueprint def-amb-p1-trace (blueprint: def-amb-p1-trace). -/
def projectiveLineTraceDatum (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    OrdinaryFiniteP1Datum A N hA (projectiveLineTraceTransport N hN A hA) S hS :=
  Classical.choose (Classical.choose_spec
    (exists_ordinaryFiniteP1Adjunction N hN A hA)) S hS

/-- Projection onto the constant second summand of the canonical decomposition:
`t_q = pr₂ ∘ b_q⁻¹`. Here `Rq_*` is the total right derived functor of module direct
image and the finite Tate line is the scalar extension of the roots-of-unity sheaf.
Source: blueprint def-amb-p1-trace (blueprint: def-amb-p1-trace). -/
def projectiveLineTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ⟶ ordinaryFiniteUnit A S :=
  (projectiveLineTraceDatum N hN A hA S hS).decomposition.inv ≫ biprod.snd

/-- The trace sends the scalar Kummer Chern class of O(1) to one.
Source: blueprint def-amb-p1-trace (blueprint: def-amb-p1-trace).
Proof: the decomposition's second component is the Chern adjunct h. Thus
h = in₂ then b, and h then b inverse then pr₂ = in₂ then pr₂ = identity. -/
theorem projectiveLineTrace_chern (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ordinaryFiniteP1ChernPushforward A N hA S
        (projectiveLineTraceDatum N hN A hA S hS).chern ≫
      projectiveLineTrace N hN A hA S hS = 𝟙 (ordinaryFiniteUnit A S) := by
  exact (projectiveLineTraceDatum N hN A hA S hS).trace_chern

/-- The map epsilon for every unbounded complex: inverse of the canonical ordered
proper projection, tensor with the normalized trace, and the tensor unit constraint.
Properness of q gives finite type, hence its source is Noetherian; these are exactly
the hypotheses of the recorded arbitrary-complex projection theorem.
Source: blueprint def-amb-p1-trace (blueprint: def-amb-p1-trace). -/
def projectiveLineTraceEpsilon (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
      ((ordinaryFiniteP1Right A N hA S).obj K) ⟶ K :=
  letI : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  letI : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  letI : IsProper (ProjectiveLine S ↘ S) :=
    ProjectiveSpace.instIsProper (ULift (Fin 2)) S
  letI : IsIso (ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K) :=
    isIso_proper_projection_formula_reordered A (ProjectiveLine S ↘ S)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K
  inv (ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K) ≫
    ((ordinaryFiniteTensor A S).obj K).map (projectiveLineTrace N hN A hA S hS) ≫
      (derivedTensorSingleUnitIso K).hom

end AlgebraicGeometry.Etale
