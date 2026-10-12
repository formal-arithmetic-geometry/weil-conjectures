/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent
import Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint
import Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule
import Sheaf.AlgebraicGeometry.AffineDerivedCohomology
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-! # FiniteAffineAdjointCounitComparison

Source: Stacks Project, Duality for Schemes, Section 48.11.
-/

@[expose] public section

universe u wX wY wA

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The finite affine comparison of geometric and scalar right adjoints at a
bounded-below quasi-coherent object. No identification with internal Hom or evaluation
at one is asserted here. The boundedness of a(K) is an explicit input.

Source: Stacks Project, Tag 0AX2, comparison-of-right-adjoints paragraph; Tag 0AVW
(blueprint: lem-sc-finite-affine-adjoint-counit-comparison).

Proof:
1. Scalar restriction is exact. On a K-injective representative, Rg_* followed by
   scalar restriction and Rf_* are the same pushforward complex, with different
   scalar structures. Descend this identity to the natural isomorphism c, on the
   whole derived category, keeping the localization comparison maps.
2. Use finite_affine_derived_equivalence to identify D_QCoh(X) with D_QCoh(A).
   The given adjunction R ⊣ a transports to the restriction functor under this
   equivalence; its counit is comparison.inv followed by adj.counit.
3. The affine sheaf-Hom adjunction computes the ambient scalar right adjoint.
   Finite pseudo-coherence and the internal-Hom quasi-coherence lemma put its value
   on K in D+_QCoh(A); uniqueness transports this assertion to the specified rhoR.
   Exact scalar restriction detects vanishing of cohomology. The affine cohomology
   formula therefore makes E preserve lower bounds; its inverse is exact on
   quasi-coherent modules and preserves them too. Thus haK bounds E(a(K)).
4. For this fixed K, both E(a(K)) and rhoR(K) represent the same contravariant
   functor M -> Hom(rho(M),K) on D+_QCoh(A), by the two given adjunctions and the
   equivalence. Pointwise uniqueness of representing objects (Yoneda) gives phi,
   transported through the Rg_* comparison. Its counit equation is the pointwise
   right-adjoint uniqueness equation. No global preservation claim for a is needed.
   The choice of comparison is used to transport the adjunction, so this also works
   for arbitrary specified comparison and adjunction, including their automorphisms.
All statements hold for the zero object and for shifts, with shifted lower bounds. -/
theorem finite_affine_adjoint_counit_comparison {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (comparison : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : R ⊣ a)
    (ρR : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
    (adjA : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ ρR)
    (K : schemeDerivedQCohCategory Y) (hK : ∃ n : ℤ, K.obj.IsGE n)
    (haK : ∃ n : ℤ, (a.obj K).obj.IsGE n) :
    ∃ c : RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f) ⋙
        (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ≅
        schemeDerivedDirectImage f,
    ∃ φ : (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)).obj
        (a.obj K).obj ≅ ρR.obj K.obj,
      (c.app (a.obj K).obj).inv ≫
        (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor.map
            φ.hom ≫ adjA.counit.app K.obj =
        comparison.inv.app (a.obj K) ≫ (adj.counit.app K).hom := by
  sorry

end AlgebraicGeometry
