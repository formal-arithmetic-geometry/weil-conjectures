/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenProjectionMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions

/-! # The proper/open tower underlying coordinate projection composition

The tower maps are constructed from proper/open mates and canonical changes of
compactification. The origin component cache records the specified compositor component
with its ambient morphism type. No projection compatibility is assumed in the data.
Source: Stacks 0F7J and the ordered affine projection calculation
(blueprint: def-pur-affine-projection-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity

set_option linter.auxLemma false in
attribute [local instance 100000] AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

/-- The actual raw proper/open tower map. Its factors are the proper/open mate,
proper direct-image composition, and open-extension composition with the endpoint cast.
Source: Stacks 0F7J (blueprint: def-pur-affine-projection-tower). -/
def projectionTowerMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} {f : X ⟶ T} {g : T ⟶ Y} [QuasiCompact f] [QuasiCompact g]
    (b : Compactification g) (e : Compactification (f ≫ b.i)) (M : C A X) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e.restrict).obj M) ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (b.comp e)).obj M :=
  letI : QuasiCompact b.i := b.quasiCompact_openImmersion inferInstance
  ((lowerStar (ModuleCat.{u + 1} A) b.g).rightDerivedFunctor).map
    ((properOpenMate A (pullback.fst e.g b.i) e.restrict.g e.g b.i
      pullback.condition).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategory.obj M)) ≫
  (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g b.g).hom.app
    ((ProperOpenShriek A (pullback.fst e.g b.i)).obj
      ((ProperOpenShriek A e.restrict.i).obj M)) ≫
  ((lowerStar (ModuleCat.{u + 1} A) (e.g ≫ b.g)).rightDerivedFunctor).map
    ((properOpenShriekComp A e.restrict.i (pullback.fst e.g b.i)).hom.app M ≫
      (properOpenShriekCongr A e.restrict_i_fst).hom.app M)

/-- Normalize the actual proper/open tower map to the three chosen compactifications.
The middle map is constructed on the pro-etale site; it is independent of
`originCompositionAmbient`. Source: Stacks 0F7J
(blueprint: def-pur-affine-projection-tower). -/
def normalizedProjectionTowerMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ Y)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (M : C A X) (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ⟶
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj M :=
  let c := HasCompactification.compactification f
  let b := HasCompactification.compactification g
  let h := HasCompactification.compactification (f ≫ g)
  let e := h.ofComp b
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      ((towerCandidateComparison A c e.restrict).hom.app ⟨M, hM⟩) ≫
    projectionTowerMap A b e M ≫
    (towerCandidateComparison A (b.comp e) h).hom.app ⟨M, hM⟩

/-- The specified origin compositor component, with its ambient morphism type cached.
This is the component of the existing natural isomorphism at the supplied witnessed
object, not a choice of a new compositor. Source: the actual origin compositor
(blueprint: def-pur-affine-projection-tower). -/
def projectionOriginComponent (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ Y)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (M : C A X) (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ⟶
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj M :=
  (originCompositionAmbient A f g).hom.app ⟨M, hM⟩

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
