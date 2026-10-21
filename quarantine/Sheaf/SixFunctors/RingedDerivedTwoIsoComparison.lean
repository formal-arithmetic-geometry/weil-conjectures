/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.SixFunctors.RingedDerivedComparisonData
import Sheaf.CategoryTheory.GeometricModuleTransport
import Sheaf.Algebra.Homology.KFlatResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Geometric 2-isomorphism normalization

Source: Stacks Project, Modules on Sites and Cohomology on Sites,
Tags 03D7, 03D8, 03EL, 07A4 and 07A6.
(blueprint: lem-sfb-ringed-derived-two-iso-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons

attribute [local irreducible] SheafOfModules.monoidalCategory

/-- Representative normalization with the right comparison fixed as the derived
adjunction mate. Hom-bijection compatibility follows formally from that choice.
Source: Stacks Project, Tags 03D7, 03D8 and 07A6.
(blueprint: lem-sfb-ringed-derived-two-iso-comparison). -/
structure TwoIsoCore {X Y : Site.{u, w}} {h k : Morphism X Y}
    (lh : Lift h) (lk : Lift k) (θ : h.inverse ≅ k.inverse) where
  ordinary : lh.edge.pullback ≅ lk.edge.pullback
  ordinary_insertion : ∀ M : Y.modules,
    lh.insertion M ≫ X.sets.map (ordinary.hom.app M) =
      θ.hom.app (Y.sets.obj M) ≫ lk.insertion M
  ordinary_right : lk.edge.pushforward ≅ lh.edge.pushforward
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv lk.edge.moduleAdjunction lh.edge.moduleAdjunction ordinary
  pullback : lh.edge.left ≅ lk.edge.left
  pullback_model : ∀ P : CochainComplex Y.modules ℤ, Y.corner.mateFlat P →
    pullback.hom.app (DerivedCategory.Q.obj P) ≫ lk.alpha P =
      lh.alpha P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary.hom (ComplexShape.up ℤ)).app P)
  pushforward_model : ∀ I : CochainComplex X.modules ℤ,
    lk.eta.app I ≫ (conjugateIsoEquiv lk.edge.derivedAdjunction
      lh.edge.derivedAdjunction pullback).hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary_right.hom (ComplexShape.up ℤ)).app I) ≫
        lh.eta.app I
  tensor : ∀ U V : Y.D,
    pullback.hom.app (Y.closed.tensor.obj (U, V)) ≫ (lk.tensor U V).hom =
      (lh.tensor U V).hom ≫ X.closed.tensor.map
        (X := (lh.edge.left.obj U, lh.edge.left.obj V))
        (Y := (lk.edge.left.obj U, lk.edge.left.obj V))
        (pullback.hom.app U, pullback.hom.app V)
  unit : pullback.hom.app Y.closed.monoidal.tensorUnit ≫ lk.unit.hom = lh.unit.hom

/-- Geometric 2-isomorphism normalization for an already normalized lift.
Source: Stacks Project, Modules on Sites and Cohomology on Sites,
Tags 03D7, 03D8, 03EL, 07A4 and 07A6.
(blueprint: lem-sfb-ringed-derived-two-iso-comparison).

Proof:
1. Transport the algebraic inverse image across the specified geometric theta.
On generalized scalar-extension generators the ordinary map sends s tensor x to
s tensor theta(x). The structural-map equality is precisely the balancing
condition, so the map is well-defined, linear, natural and invertible. This gives
ordinary and its insertion equation.
2. The two underlying geometric Hom bijections and the scalar-insertion formula
identify the ordinary direct-image comparison with the adjunction mate of
ordinary. Use this mate as ordinary_right.
3. Both ordinary pullbacks preserve the K-flat resolving class. Localizing the
ordinary map gives pullback and pullback_model. The universal right-derived
property applied to ordinary_right gives pushforward and its eta normalization
on every complex.
4. The two routes in the tensor square have the same values on generalized pure
tensors: theta acts on each module factor and preserves their tensor pairing.
The two routes on the unit are the same scalar action by ring compatibility.
Localize these equations, use the lift's canonical tensor and unit equations,
and extend from resolving representatives by naturality.
5. The ordinary mate equation gives equality of the ordinary transposes. Apply
the canonical derived Hom formulas on K-flat/K-injective representatives; the eta
normalization and pullback_model identify their two sides. Fraction
representations and resolutions extend the equality to every derived morphism,
which identifies the right-derived comparison with the specified adjunction mate
and proves pushforward_model. The specified theta, rather than an
unspecified equivalence of inverse images, is used throughout. -/
theorem twoIsoComparison_exists {X Y : Site.{u, w}} {h k : Morphism X Y}
    (lh : Lift h) (lk : Lift k) (θ : h.inverse ≅ k.inverse)
    (hθ : h.ringMap = θ.hom.app
      ((sheafCompose Y.J (CategoryTheory.forget CommRingCat.{u})).obj Y.A) ≫ k.ringMap) :
    Nonempty (TwoIsoCore lh lk θ) := by sorry

end CategoryTheory.RingedDerivedComparisons
