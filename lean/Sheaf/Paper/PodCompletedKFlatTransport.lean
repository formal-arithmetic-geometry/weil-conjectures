/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Sheaf.Paper.SemilinearSystemModels
import Sheaf.Paper.PodCompletedOrdinaryTensor
import all Sheaf.Paper.SemilinearTensorEvaluation
import all Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat

/-! # Completed coefficient reindexing on tensor representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
open SemilinearSections
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- Exact completed-coefficient reindexing preserves flat-term K-flat representatives.
Source: blueprint prop-pod-dual-tate-data-compatibility Step 5, simultaneous resolution
transport; Stacks 06YP and 07A4.
(blueprint: lem-pod-completed-kflat-transport).
Proof: reverse reindexing gives the inverse exact module equivalence. Its ordinary
tensor comparison is induced by relabeling pure tensors. In each total degree,
reindexing preserves the coproduct indexed by pairs of integers, and preserves each
signed differential. Hence it identifies the tensor total complex with the tensor of
the reindexed complexes. Given an acyclic complex on X, reverse reindex it to Y;
exactness preserves acyclicity. The K-flat tensor test on Y is acyclic, so its exact
reindexing is acyclic on X. The unit and counit of the equivalence identify this with
the required tensor test. This applies to unbounded complexes and to the empty site;
no levelwise detection of derived morphisms or residue-field assumption is used. -/
theorem podCompletedKFlatTransport
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) P)
    (_hflat : flatTerms.{u + 1, u, u} (Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      (((podCompletedModuleInverseImage l E g).mapHomologicalComplex (.up ℤ)).obj P) := by
  let RX := completedIntegralCommRingSheafUnrestricted l E X
  let RY := completedIntegralCommRingSheafUnrestricted l E Y
  let F := podCompletedModuleInverseImage l E g
  let : F.IsEquivalence := (podCompletedInverseImage_equivalence l E g).1
  let e := F.asEquivalence
  let : e.functor.Additive := inferInstanceAs F.Additive
  let : e.inverse.Additive := e.inverse_additive
  let H := F.mapHomologicalComplex (.up ℤ)
  let G := e.inverse.mapHomologicalComplex (.up ℤ)
  let := SheafOfModules.isMonoidal_W_independentCoefficients RX
  let := SheafOfModules.isMonoidal_W_independentCoefficients RY
  let := SheafOfModules.monoidalCategory RX
  let := SheafOfModules.monoidalCategory RY
  obtain ⟨μ, hn, _⟩ := podCompletedOrdinaryTensor_exists l E g
  let τ := exactTensorTotalIso F μ hn e.inverse e.toAdjunction
  intro Z hZ
  have hG : (G.obj Z).Acyclic := (Equivalence.acyclic_map_iff e.inverse Z).mp hZ
  have hP' := hP (G.obj Z) hG
  have hF := (Equivalence.acyclic_map_iff F _).mp hP'
  let i := (τ.app (G.obj Z, P)).symm ≪≫
    (totalTensor.{u + 1, u, u} (Scheme.ProEt.topology X) RX).mapIso
      (Iso.prod ((e.mapHomologicalComplex (.up ℤ)).counitIso.app Z) (Iso.refl (H.obj P)))
  exact Equivalence.acyclic_of_iso i hF


end WeilConjectures
