/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Algebra.Homology.AffinePushforwardComparisonCoordinates

/-! # Normalized affine cohomology edge maps -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Every component of a normalized affine edge morphism is invertible.
Source: Stacks Project, perfect.tex, lemma-affine-morphism-equivalence (Tag 0AVW),
and perfect.tex, lemma-application-nice-K-injective (Tag 08D4).
(blueprint: lem-pc-affine-pushforward-cohomology-edge-isIso).

Proof: For a complex C of A-modules, associated sheaves and their kernels, images
and cohomology are quasi-coherent. Affine higher-direct-image vanishing, with
bound one in the unbounded truncation comparison of Tag 08D4, shows that the
right-derived pushforward unit on T_A C induces an isomorphism in each degree.
Every other factor of q is an isomorphism (exact tilde and scalar restriction,
the Q/homology comparison, and σ), so q is invertible. The normalization equation
for the identity representative says q = (T_B res_phi)(b) followed by α at Q(T_A C).
Since b is an isomorphism, this component of α is invertible. Every object of
D_QCoh(Spec A) is isomorphic to Q(T_A C), by the affine derived equivalence of
Tag 06Z0. Naturality of α along this isomorphism expresses its remaining component
as a composite of invertible maps. Thus every component is invertible. This works
for unbounded C and for the zero ring; it does not require an arbitrary α to agree
with the normalized edge map without the displayed normalization hypothesis. -/
theorem affinePushforwardCohomologyEdge_isIso
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))) :
  ∀ (α : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B) ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i),
    (∀ (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (L : schemeDerivedQCohCategory (Spec (.of A)))
      (t : DerivedCategory.Q.obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L.obj),
      (∃ h : DerivedCategory.Q.obj
          (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C) = L.obj,
        t.hom = eqToHom h) →
      affinePushforwardCohomologyMapOfComparison A B φ σ C i ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map t.hom) =
        (affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
          (affinePushforwardRepresentativeCohomologyIso A C L.obj t i).hom) ≫ α.app L) →
    ∀ L, IsIso (α.app L) := by
  sorry

end AlgebraicGeometry
