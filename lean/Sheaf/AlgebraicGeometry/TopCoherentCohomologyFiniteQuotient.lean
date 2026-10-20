/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Paper.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Sheaf.AlgebraicGeometry.TopDegreeOpenRestrictionSurjective
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The geometric part of top-cohomology finiteness supplies a finite-dimensional
vector space mapping onto the top coherent cohomology group. The source is a
finite direct sum of copies of `k`; in the geometric proof it comes from the
finite-dimensional top cohomology of a projective closure, followed by the
restriction and comparison maps. The same construction records the proper
surjective Chow modification used to reach that projective closure.

Source: Stacks Project, Étale Cohomology, Tag 0A3M, proof of
`lemma-top-cohomology-coherent`, steps 7--8.
(blueprint: lem-weil-pbc-top-coherent-cohomology-finite-quotient).
Proof: apply Chow modification and projective closure. The top cohomology of the
projective closure is finite-dimensional; top-degree restriction is surjective,
and Leray comparison identifies its target with the cohomology group displayed
here. Choosing a finite basis gives the map from `Fin n → k`.
-/
theorem exists_finiteDimensional_top_coherent_cohomology_quotient
    (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (d : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    ∃ n : ℕ, ∃ f : (Fin n → k) →ₗ[k]
      ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (X ↘ Spec (.of k)).appTop).hom).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace d).obj F)),
      Function.Surjective f ∧
        ∃ (Y : Scheme.{u}) (π : Y ⟶ X), IsProper π ∧ Surjective π := by
  sorry

end AlgebraicGeometry
