/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProperFiniteFibreFiniteNeighbourhood

/-!
# Projective morphisms with zero-dimensional generic fibre

Source: the Weil conjectures blueprint, chapter `sec-smooth-purity`, unit `sk-prop-sf-cbc`,
lemma `lem-fin-projective-generically-finite` (blueprint: lem-fin-projective-generically-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A projective morphism over a Noetherian domain with generic fibre of dimension at most
zero is finite over a nonempty open of the base.

Source: the Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-cbc`,
lemma `lem-fin-projective-generically-finite` (blueprint: lem-fin-projective-generically-finite).

Proof:
1. At the generic point eta = (0), the local ring and residue field are K. Thus the base
   change displayed below is the scheme-theoretic fibre [def-pc-scheme-fibre]. Projectivity
   is preserved by base change [lem-pc-projective-base-change] and implies properness
   [lem-pc-projective-proper]. Properness gives finite type [def-weil-proper-morphism,
   def-weil-finite-type-morphism]. Dimension at most zero then makes the generic fibre
   finite [lem-weil-pbc-finite-type-dim-zero-artinian]. The fibre homeomorphism identifies
   its points with the ordinary fibre over eta [def-pc-scheme-fibre].
2. The base Spec A is locally Noetherian [pqf-def-locnoeth]. Apply
   [thm-sc-proper-finite-fibre-finite-neighbourhood] to this proper morphism at eta to
   obtain an open neighbourhood U with finite restriction.
3. Since eta belongs to U, the open U is nonempty, as required.
-/
theorem exists_nonempty_open_isFinite_restrict_of_isProjective_generic_dim_le_zero
    (A K : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {D : Scheme.{u}} (f : D ⟶ Spec (.of A)) [IsProjective f]
    (h : topologicalKrullDim
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K))) : Scheme.{u}) ≤ 0) :
    ∃ U : (Spec (.of A)).Opens, (U : Set (Spec (.of A))).Nonempty ∧
      IsFinite (f ∣_ U) := by
  sorry

end AlgebraicGeometry
