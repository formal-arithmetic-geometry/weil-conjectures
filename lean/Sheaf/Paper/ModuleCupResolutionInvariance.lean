/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
import Sheaf.Paper.ModuleCupDerivedTensorConnectivity
import Sheaf.Paper.ModuleCupHZeroIdentification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility
import Sheaf.Paper.ModuleCupCanonicalHZeroIdentification

/-! # Independence of resolution pairings on cohomology

Source: Stacks Project, Cohomology of Sheaves, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-resolution-invariance)
-/

@[expose] public section

universe uM
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Products of representatives with equal input classes have equal output
classes, even when the representatives belong to different computing pairings.
No bilinear cup product is assumed or constructed in this statement.
Source: Stacks Project, Section 20.31 (0FKU), Lemma 20.31.3 and Tag 0FKV.
(blueprint: lem-sc-module-cup-resolution-invariance)
Proof: a restriction-compatible O-linear pairing with Leibniz is a morphism
from the signed total tensor of the two resolution complexes to the target
complex. Precompose with the canonical morphism from derived tensor to naive
tensor, and identify the three complexes with F, G and F tensor G via their
augmentations. This gives a morphism F tensor-derived G to F tensor G in the
sheaf derived category. F tensor-derived G is in nonpositive degrees; the target
is concentrated in degree zero. The truncation adjunction identifies morphisms
between these objects with morphisms H-zero(F tensor-derived G) to F tensor G.
H-zero is the ordinary tensor F tensor G. The augmentation_pair condition
identifies the latter morphism with the identity, for both D and E. Hence their
derived morphisms coincide. Apply derived global sections and the compatibility
of naive cup with derived cup (Lemma 20.31.3 for the map to the one-point ringed
space). The input and output comparison maps are precisely those extending the
augmentations in CupAcyclicResolution, so taking cohomology uses its class maps.
The equalities of input classes therefore imply equality of the output classes.
The argument needs neither flat coefficients nor termwise flat resolutions. -/
theorem moduleCup_resolution_invariance {X : Scheme.{uM}} {F G : X.Modules}
    (D E : CupResolutionPairing F G) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (a' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.left.K).sc p).moduleCatLeftHomologyData.K)
    (b' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.right.K).sc q).moduleCatLeftHomologyData.K)
    (c' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (ha : D.left.class p a = E.left.class p a')
    (hb : D.right.class q b = E.right.class q b')
    (hc : c.val = D.pair p q ⊤ a.val b.val)
    (hc' : c'.val = E.pair p q ⊤ a'.val b'.val) :
    D.target.class (p + q) c = E.target.class (p + q) c' := by sorry

end
end AlgebraicGeometry.Scheme.Modules
