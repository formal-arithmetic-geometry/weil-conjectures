/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # A module model on one principal open

Source: Stacks Project, Tag 08E7, local-model comparison in the converse direction
(blueprint: lem-pc-affine-pseudo-coherent-principal-model).
-/

@[expose] public section

universe u wX wL

open CategoryTheory

namespace AlgebraicGeometry

/-- A bounded-above finite-free sheaf model on an open neighbourhood gives a
pseudo-coherent localized module complex on every principal open contained in it.

Source: Stacks Project, Tag 08E7, local-model comparison, using the affine derived
comparison of Tag 06Z0
(blueprint: lem-pc-affine-pseudo-coherent-principal-model).

Proof:
Restrict P along D(f) ≤ U. Restriction is exact, preserves zero objects and finite
free sheaves, and sends the given derived isomorphism to one on D(f). Identify
D(f) with Spec(A_f). The sections of tilde N on principal opens are localizations
of N, naturally in N; hence restriction of the termwise tilde complex of M
identifies with the termwise tilde complex of A_f tensor M. The finite free terms
of the restricted P correspond under the tilde/Gamma adjunction to finite free
A_f-modules of the same ranks. Full faithfulness lifts every differential, and
faithfulness proves that consecutive differentials compose to zero. This gives
a module complex with the same upper bound. Both associated-sheaf complexes have
quasi-coherent cohomology; the full inclusion of the quasi-coherent derived
category lifts their isomorphism, and the affine derived equivalence reflects it
to an isomorphism of module derived objects. Reverse this isomorphism to obtain
the finite-free representative required by DerivedCategory.IsPseudoCoherent.
If D(f) is empty, A_f is the zero ring, all its modules are zero, and the zero
complex is the representative. Rank zero and arbitrarily negative upper bounds
are allowed throughout. This argument makes no assertion about a finite cover
or about gluing models from different opens. -/
theorem affine_pseudoCoherent_principal_model (A : Type u) [CommRing A]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A)
    [HasDerivedCategory.{wL} (ModuleCat.{u} (Localization.Away f))]
    (U : (Spec (.of A)).Opens)
    (hf : PrimeSpectrum.basicOpen f ≤ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings (Spec (.of A)).toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hiso : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M)) ≅
      DerivedCategory.Q.obj P)) :
    DerivedCategory.IsPseudoCoherent
      (DerivedCategory.Q.obj ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away f)))
        (ComplexShape.up ℤ)).obj M)) := by sorry

end AlgebraicGeometry
