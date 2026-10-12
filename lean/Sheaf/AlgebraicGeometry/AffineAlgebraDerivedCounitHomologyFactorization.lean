/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.AffineDerivedCohomology
import Sheaf.AlgebraicGeometry.AffineModuleCorrespondence
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral

/-! # Cohomology of the affine algebra derived counit

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- Under the cohomology comparison, the derived affine algebra counit is the
underived counit applied to the cohomology module.
Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
(blueprint: lem-sc-affine-algebra-derived-counit-homology-factorization).

Proof: For the tensor-derived adjunction, flatness of the stalk localizations of g
makes pullback exact, giving H^n(Lg-star E) = g^*H^n(E) naturally in E.
For K with quasi-coherent cohomology, compare Rg-star with Rf-star by exact scalar
restriction to O_Y using the same K-injective resolution. The affine unbounded
cohomology calculation gives H^n(Rg-star K) = g_*H^n(K); the equality is algebra
linear, since the comparison uses the same pushed complex with its natural
f_*O_X action. Applying exact pullback gives the displayed source comparison.
On the chosen resolutions the derived counit is induced by the ordinary
counit. The natural kernel and image comparisons used to compute cohomology
identify this map with the evaluation g^*g_*H^n(K) to H^n(K). On affine opens
this sends the pure tensor of a ring section and a module section to their
product, so it is the ordinary tensor adjunction counit; naturality in open
restriction identifies the sheaf maps. Finally uniqueness of the underived
and derived left adjoints supplies adjunction-compatible isomorphisms to P and L.
Absorb their cohomology components in the source isomorphism e; the target
H^n(K) is unchanged, yielding precisely the equation for a and adj.
The unbounded cohomology formula is required: arbitrary direct image is not
claimed exact. Zero cohomology, empty schemes and the identity morphism satisfy
the same formula, with no extra hypotheses. -/
theorem affine_algebra_derived_counit_homology_factorization
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    [Limits.PreservesFiniteLimits P]
    (L : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) ⥤
      schemeDerivedCategory X)
    (adj : L ⊣ RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f))
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K) (n : ℤ) :
    ∃ e : (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).obj
          (L.obj ((RingedSpace.derivedModuleDirectImage
            (toDirectImageAlgebraSpace f)).obj K)) ≅
        P.obj ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).obj K)),
      (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).map
          (adj.counit.app K) =
        e.hom ≫ a.counit.app ((DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).obj K) := by sorry

end AlgebraicGeometry
