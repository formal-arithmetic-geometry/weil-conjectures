/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.AffinePushforwardComparisonCoordinates
import Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdge

/-! Identity-representative affine cohomology edge normalization. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules (moduleRings Y.toRingedSpace))]

/-- The affine edge equation for the canonical representative. The proof is the
identity-representative part of the affine cohomology edge construction, using
Stacks Project, perfect.tex, Tags 0AVW and 08D4.
(blueprint: lem-pc-affine-pushforward-cohomology-edge-identity).

Proof: construct the edge transformation from the sheaf-level edge, the supplied
ordinary comparison, and the tilde/Gamma counit. Exactness of tilde identifies
cohomology of the canonical representative; naturality and the adjunction
triangle identity reduce the coordinate composite to the derived-unit edge.
This is the canonical-representative restriction of the full normalization. -/
theorem exists_affinePushforwardCohomologyEdge_identity
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))) :
  ∃ α : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B) ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules (moduleRings (Spec (.of B)).toRingedSpace)) i,
    ∀ (C : CochainComplex (ModuleCat A) ℤ)
      (hK : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C))),
      affinePushforwardCohomologyMapOfComparison A B φ σ C i ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map
            (𝟙 _)) =
        (affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
          (affinePushforwardRepresentativeCohomologyIso A C _ (Iso.refl _) i).hom) ≫
          α.app ⟨_, hK⟩ := by
  sorry

end AlgebraicGeometry
