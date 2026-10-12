/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.AffinePseudoCoherentCriterion
import Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion
import Sheaf.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor

/-! # Finite Tor amplitude of the affine module model -/

@[expose] public section

universe u w wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A perfect affine object has a pseudo-coherent finite-Tor preimage under the
associated-sheaf derived equivalence.
Source: Stacks Project, perfect.tex, Lemma perfect-lemma-perfect-affine (Tag 08EB).
(blueprint: lem-pc-perfect-affine-module-preimage)

Proof: Take the equivalence of lem-pc-affine-qcoh-derived-equivalence and set
C = e.inverse.obj E. Its counit, followed by the inclusion, gives E ≅ e(C).
Choose a complex M representing C using essential surjectivity of Q. The comparison
Q ⋙ e ⋙ inclusion ≅ tilde ⋙ Q identifies its associated sheaf with E.
Perfectness gives pseudo-coherence and local finite Tor dimension by
lem-pc-perfect-pseudo-coherent-locally-finite-tor. A finite subcover of Spec A supplies
one interval: take the minimum of the finitely many lower bounds and the maximum of
upper bounds, enlarging to a nonempty interval if the spectrum is empty. Derived tensor
commutes with restriction, and vanishing on an open cover detects zero cohomology sheaves.
Thus E has global finite Tor amplitude. Apply lem-pc-affine-pseudo-coherent-criterion
and lem-pc-affine-tor-amplitude-criterion to M, and transport along Q(M) ≅ C.
For the zero ring the spectrum is empty and both derived categories are zero, so the
interval [0,0] works. This step constructs no bounded projective replacement. -/
theorem perfect_affine_module_preimage (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u}
        ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (hE : Scheme.IsPerfect (Spec (.of A)) E.obj) :
    ∃ e : DerivedCategory (ModuleCat.{u} A) ≌ schemeDerivedQCohCategory (Spec (.of A)),
      ∃ C : DerivedCategory (ModuleCat.{u} A),
        DerivedCategory.IsPseudoCoherent C ∧
        (∃ a b : ℤ, a ≤ b ∧
          DerivedCategory.torAmplitudeIn (ModuleCat.{u} A) a b C) ∧
        Nonempty (E.obj ≅ ((schemeDerivedQCohProperty (Spec (.of A))).ι).obj
          (e.functor.obj C)) ∧
        Nonempty (DerivedCategory.Q ⋙ e.functor ⋙
          (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
          @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) := by
  sorry

end AlgebraicGeometry
