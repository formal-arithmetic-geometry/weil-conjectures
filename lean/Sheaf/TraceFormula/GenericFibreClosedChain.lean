/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.ZetaSeries
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# A maximal chain from the generic point to a closed point

Source: Stacks Project, Morphisms, Tag 02JX, lemma-alteration-dimension,
proof of the equality clause (blueprint: lem-trf-generic-fibre-closed-chain).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- The structural map from a field to the function field of an integral scheme.

Source: Stacks Project, Morphisms, Tag 02JX, equality clause
(blueprint: lem-trf-generic-fibre-closed-chain).
-/
noncomputable def functionFieldBaseRingHom {K : Type u} [Field K]
    {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsIntegral X] :
    K →+* X.functionField :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ (X ↘ Spec (.of K)).appTop ≫
    @Scheme.germToFunctionField X _ ⊤ ⟨⟨genericPoint X, trivial⟩⟩).hom

/-- A finite-type integral scheme over a field has a closed point at the end of a
maximal specialization chain from its generic point, of length the transcendence
 degree of its function field. Its endpoint has finite residue-field extension.

Source: Stacks Project, Morphisms, Tag 02JX, lemma-alteration-dimension, proof of the
 equality clause: a Jacobson closed point, finite residue extension, and a maximal
 local prime chain. The dimension computation uses Algebra, Tag 00P0.
(blueprint: lem-trf-generic-fibre-closed-chain).

Proof:
1. Apply the Jacobson-space result for a locally finite-type scheme over a field to
   choose a closed point of the nonempty scheme.
2. Choose an affine finite-type chart containing it. Its maximal residue field is
   finite over the base field, and the chart and scheme stalks agree at that point.
3. The generic point lies in the chart, whose fraction field is the scheme function
   field. The finite-type domain dimension theorem identifies its dimension and the
   maximal localization dimension with the transcendence degree.
4. A maximal prime chain in the localization contracts to a strict prime chain in the
   chart by the localization prime correspondence.
5. The chain cannot be extended at either end, so it starts at the zero prime and ends
   at the maximal ideal. These primes are the generic and closed points, and strict
   inclusions give the required successive specializations. This also covers length
   zero.
-/
theorem exists_generic_fibre_closed_chain
    {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] :
    ∃ r : ℕ,
      @Algebra.trdeg K X.functionField _ _
          ((functionFieldBaseRingHom (K := K) (X := X)).toAlgebra) = (r : Cardinal) ∧
      ∃ (x : X) (ξ : Fin (r + 1) → X),
        x ∈ closedPoints (X : Type u) ∧
        ξ 0 = genericPoint X ∧
        ξ (Fin.last r) = x ∧
        (∀ i : Fin r,
          (ξ i.castSucc) ⤳ (ξ i.succ) ∧ ξ i.castSucc ≠ ξ i.succ) ∧
        @Module.Finite K (X.residueField x) _ _
          ((X ↘ Spec (.of K)).residueFieldAlgebraMap x).toAlgebra.toModule := sorry

end AlgebraicGeometry
