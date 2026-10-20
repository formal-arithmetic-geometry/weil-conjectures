/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.Algebra.Homology.SheafComplexDerivedTensorVanishes
public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons
public import Sheaf.AlgebraicGeometry.FiniteTorDimensionOver
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.InverseImageStructureStalkIso
import WeilConjectures.AlgebraicGeometry.RelativeInverseImageStalkRestriction
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Sheaf.Algebra.Homology.StalkKFlatTensorHomology
import WeilConjectures.Topology.RingedModuleSkyscraper
import WeilConjectures.Topology.SkyscraperComplexStalk
import WeilConjectures.Topology.InverseImageStalk
import Sheaf.Algebra.Homology.RelativeTorAmplitudeLocalization
import WeilConjectures.Topology.InverseImageModule

/-! # Relative Tor amplitude on an affine scheme

Source: Stacks Project, Tag 0DHY, lemma-tor-dimension-rel-affine, both clauses;
Tags 09U9, 009A and 008H for the equivalent inverse-image module test
(blueprint: lem-trf-affine-relative-tor-amplitude-criterion).

## Main statements

* `affine_relative_torAmplitude_iff`: the fixed-interval affine criterion.
* `affine_relative_torAmplitude_inverseImage_test`: inverse-image sheaves suffice.
* `affine_relative_locallyFiniteTor_iff`: the local finite-dimension criterion.
-/

@[expose] public section

universe u wR wU

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

/-- Restrict the actual tilde complex along the canonical inverse-image structure map.
Source: Stacks Project, Tag 0DHY
(blueprint: lem-trf-affine-relative-tor-amplitude-criterion). -/
def affineRelativeTorComplex {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (Spec (.of A)))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (TopCat.Sheaf.inverseImageRing (Spec.map (CommRingCat.ofHom φ)).base
            (Spec (.of R)).sheaf))) ℤ :=
  let F := SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology (Spec (.of A)))
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (Scheme.Modules.tensorPullbackRingMap (Spec.map (CommRingCat.ofHom φ))))
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((affineModelTildeComplex (.of A)).obj M)

/-- The canonical open restriction of the termwise tilde complex.
Source: Stacks Project, Tag 0DHY, clause (2)
(blueprint: lem-trf-affine-relative-tor-amplitude-criterion). -/
def affineTorOpenTildeComplex {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (U : (Spec (.of A)).Opens) :
    CochainComplex (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
  let F := SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  letI : F.Additive := Functor.additive_of_preserves_binary_products F
  (F.mapHomologicalComplex (.up ℤ)).obj ((affineModelTildeComplex (.of A)).obj M)

/-- Relative sheaf Tor amplitude is exactly module Tor amplitude over the base ring.
No flatness, finiteness, boundedness or Noetherian assumption is imposed.
Source: Stacks Project, Tag 0DHY, clause (1)
(blueprint: lem-trf-affine-relative-tor-amplitude-criterion).

Proof:
1. Resolve the scalar-restricted tilde complex by a K-flat complex
   (lem-pc-kflat-resolution). At q over p identify the inverse-image ring stalk with
   R_p (lem-pc-inverse-image-structure-stalk-iso), and the tilde stalk with M_q
   (lem-weil-pbc-spec-tilde-stalk-localization). Scalar restriction agrees with the
   scheme stalk map (lem-pc-relative-inverse-image-stalk-restriction); exactness of
   stalks (lem-weil-pbc-module-stalk-exact) preserves the resolution.
2. The stalk tensor comparison (lem-pc-stalk-kflat-tensor-homology) identifies the
   tensor cohomology stalk with H^i(M_q tensor-derived over R_p F_q). Stalks detect
   vanishing. Conversely every stalk module is realized by a skyscraper sheaf
   (def-pc-ringed-module-skyscraper, lem-pc-skyscraper-complex-stalk-recovery).
3. Apply lem-trf-relative-tor-amplitude-localization (Stacks 0B67) to identify these
   localized module bounds with Tor amplitude of M over R. This uses no absolute
   Tor amplitude over A. Empty Spec A and the zero complex satisfy every interval. -/
theorem affine_relative_torAmplitude_iff
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (_hab : a ≤ b) :
    (∀ (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (Spec (.of A)))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (TopCat.Sheaf.inverseImageRing (Spec.map (CommRingCat.ofHom φ)).base
            (Spec (.of R)).sheaf))) (i : ℤ), i < a ∨ b < i →
      CochainComplex.sheafDerivedTensorVanishes
        (TopCat.Sheaf.inverseImageRing (Spec.map (CommRingCat.ofHom φ)).base
          (Spec (.of R)).sheaf) (affineRelativeTorComplex φ M) F i) ↔
      DerivedCategory.torAmplitudeIn (ModuleCat.{u} R) a b
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) := by
  sorry

/-- Testing relative Tor amplitude only on inverse images of arbitrary base module
sheaves is equivalent to testing all inverse-image-ring modules.
Source: Stacks Project, Tag 0DHY, with the stalk test of Tag 09U9 and skyscrapers
of Tags 009A and 008H (blueprint: lem-trf-affine-relative-tor-amplitude-criterion).

Proof: the all-sheaf condition implies its inverse-image restriction. Conversely,
fix q over p and a module L over R_p. Take the skyscraper G at p with stalk L
(def-pc-ringed-module-skyscraper, lem-pc-skyscraper-complex-stalk-recovery).
The inverse-image stalk formula (lem-weil-pbc-topological-inverse-image-stalk)
identifies (f inverse-image G)_q with L. This is linear over the inverse-image
ring stalk: both scalar actions multiply representatives on common neighbourhoods
(def-pc-topological-inverse-image-module). The tensor stalk comparison of Step 2
of affine_relative_torAmplitude_iff then gives vanishing against every stalk module.
Stalk detection gives the all-sheaf condition, even for a nonsurjective f and
non-quasi-coherent G. -/
theorem affine_relative_torAmplitude_inverseImage_test
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (_hab : a ≤ b) :
    (∀ (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (Spec (.of A)))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (TopCat.Sheaf.inverseImageRing (Spec.map (CommRingCat.ofHom φ)).base
            (Spec (.of R)).sheaf))) (i : ℤ), i < a ∨ b < i →
      CochainComplex.sheafDerivedTensorVanishes
        (TopCat.Sheaf.inverseImageRing (Spec.map (CommRingCat.ofHom φ)).base
          (Spec (.of R)).sheaf) (affineRelativeTorComplex φ M) F i) ↔
    (∀ (G : SheafOfModules.{u} (moduleRings (Spec (.of R)).toRingedSpace)) (i : ℤ),
      i < a ∨ b < i → CochainComplex.sheafDerivedTensorVanishes
        (TopCat.Sheaf.inverseImageRing (Spec.map (CommRingCat.ofHom φ)).base
          (Spec (.of R)).sheaf) (affineRelativeTorComplex φ M)
        (TopCat.Sheaf.inverseImageModule (Spec.map (CommRingCat.ofHom φ)).base
          (Spec (.of R)).sheaf G) i) := by
  sorry

/-- Local finite relative Tor dimension on `Spec A` is finite Tor amplitude over R.
Open restriction is the canonical exact restriction of module sheaves; finite Tor
on each neighbourhood uses the recorded inverse-image-ring definition.
Source: Stacks Project, Tag 0DHY, clause (2)
(blueprint: lem-trf-affine-relative-tor-amplitude-criterion).

Proof:
1. Choose neighbourhoods and their finite relative intervals. Apply K-flat resolution,
   the tensor stalk comparison and skyscraper recovery on each neighbourhood as in
   affine_relative_torAmplitude_iff. Restriction leaves the stalk module and scalar
   action unchanged, so each neighbourhood supplies one interval on all its stalks.
2. Spec A is quasi-compact (lem-weil-pbc-affine-scheme-qcqs), so a finite subcover
   supplies a common interval, by taking the minimum lower and maximum upper bound.
   Stalk detection gives the global relative bound. If Spec A is empty use [0,0].
3. The fixed-interval criterion gives finite Tor amplitude over R. Conversely a
   finite R interval gives a global relative interval, and the entire scheme is a
   neighbourhood of every point. The identity ring map recovers the absolute case;
   no assumption on the ring map or on the size of the complex is used. -/
theorem affine_relative_locallyFiniteTor_iff
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [∀ U : (Spec (.of A)).Opens, HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (∀ x : Spec (.of A), ∃ U : (Spec (.of A)).Opens, x ∈ U ∧
      Scheme.HasFiniteTorDimensionOver (U.ι ≫ Spec.map (CommRingCat.ofHom φ))
        (DerivedCategory.Q.obj (affineTorOpenTildeComplex M U))) ↔
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn (ModuleCat.{u} R) a b
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) := by
  sorry

end

end AlgebraicGeometry
