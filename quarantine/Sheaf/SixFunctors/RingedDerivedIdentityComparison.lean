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

/-! # Identity normalization

Source: Stacks Project, Modules on Sites and Cohomology on Sites,
Tags 03D7, 03D8, 0D6D, 0D6E and 07A6.
(blueprint: lem-sfb-ringed-derived-identity-comparison).
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
(blueprint: lem-sfb-ringed-derived-identity-comparison). -/
structure IdentityCore {X : Site.{u, w}} {f : Morphism X X} (l : Lift f)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))) where
  ordinary : l.edge.pullback ≅ 𝟭 X.modules
  ordinary_insertion : ∀ M : X.modules,
    l.insertion M ≫ X.sets.map (ordinary.hom.app M) = θ.hom.app (X.sets.obj M)
  ordinary_right : l.edge.pushforward ≅ 𝟭 X.modules
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv l.edge.moduleAdjunction (Adjunction.id (C := X.modules)) ordinary.symm
  pullback : l.edge.left ≅ 𝟭 X.D
  pullback_model : ∀ P : CochainComplex X.modules ℤ, X.corner.mateFlat P →
    ∃ a : (l.edge.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ P,
      (∀ n : ℤ, a.f n = ordinary.hom.app (P.X n)) ∧
      pullback.hom.app (DerivedCategory.Q.obj P) = l.alpha P ≫ DerivedCategory.Q.map a
  pushforward_model : ∀ I : CochainComplex X.modules ℤ,
    ∃ a : (l.edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ I,
      (∀ n : ℤ, a.f n = ordinary_right.hom.app (I.X n)) ∧
      l.eta.app I ≫ (conjugateIsoEquiv l.edge.derivedAdjunction (Adjunction.id (C := X.D))
        pullback.symm).hom.app (DerivedCategory.Q.obj I) = DerivedCategory.Q.map a
  tensor : ∀ U V : X.D,
    (l.tensor U V).hom ≫ X.closed.tensor.map
        (X := (l.edge.left.obj U, l.edge.left.obj V)) (Y := (U, V))
        (pullback.hom.app U, pullback.hom.app V) =
      pullback.hom.app (X.closed.tensor.obj (U, V))
  unit : l.unit.hom = pullback.hom.app X.closed.monoidal.tensorUnit

/-- Identity normalization for an already normalized lift.
Source: Stacks Project, Modules on Sites and Cohomology on Sites,
Tags 03D7, 03D8, 0D6D, 0D6E and 07A6.
(blueprint: lem-sfb-ringed-derived-identity-comparison).

Proof:
1. The identity geometric Hom bijection and the structural-map equation identify
scalar insertion with the identity on underlying modules. Scalar multiplication
contracts the extension-of-scalars factor to give ordinary. The underlying Hom
formula identifies ordinary_right with its mate to the identity adjunction.
2. Localize ordinary on flat-term K-flat complexes. This gives pullback with its
componentwise chain-map formula. The universal right-derived property localizes
ordinary_right and identifies pushforward on all complexes by its displayed eta
formula; no ordinary preservation of K-injectives is required.
3. On pure tensors the comparison is the identity tensor map and on the
coefficient unit it is the scalar action. The tensor and unit normalizations of
the lift therefore give the displayed tensor and unit equations on resolving
representatives. Naturality extends them to arbitrary derived objects.
4. On K-flat/K-injective representatives, the lift's canonical transpose formula
is the ordinary identity Hom bijection after the two comparisons. Fraction
representations and resolutions extend this equality to all sources and targets,
identifying the right-derived comparison with the adjunction mate and giving
pushforward_model. -/
theorem identityComparison_exists {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u)))
    (hθ : f.ringMap = θ.hom.app
      ((sheafCompose X.J (CategoryTheory.forget CommRingCat.{u})).obj X.A)) :
    Nonempty (IdentityCore l θ) := by sorry

end CategoryTheory.RingedDerivedComparisons
