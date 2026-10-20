/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.SixFunctors.RingedDerivedComparisonData
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Algebra.Homology.KFlatResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Normalized composition comparisons before the counit consequence

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0D6E, 07A6 and 0FPI.
(blueprint: lem-sfb-ringed-derived-composition-comparison).
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

/-- The tensor and representative clauses for composition; the right comparison
is explicitly the adjunction mate of the left comparison.
Source: Stacks Project, Tags 0D6D, 0D6E, 07A6 and 0FPI.
(blueprint: lem-sfb-ringed-derived-composition-comparison). -/
structure CompositionCore {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse) where
  ordinary : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback
  ordinary_insertion : ∀ M : Z.modules,
    lk.insertion M ≫ X.sets.map (ordinary.hom.app M) =
      θ.hom.app (Z.sets.obj M) ≫ f.inverse.map (lg.insertion M) ≫
        lf.insertion (lg.edge.pullback.obj M)
  ordinary_right : lk.edge.pushforward ≅ lf.edge.pushforward ⋙ lg.edge.pushforward
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv lk.edge.moduleAdjunction
      (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) ordinary.symm
  pullback : lk.edge.left ≅ lg.edge.left ⋙ lf.edge.left
  pullback_model : ∀ (P : CochainComplex Z.modules ℤ), Z.corner.mateFlat P →
    pullback.hom.app (DerivedCategory.Q.obj P) ≫
      lf.edge.left.map (lg.alpha P) ≫
      lf.alpha ((lg.edge.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
    lk.alpha P ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ordinary.hom (ComplexShape.up ℤ)).app P)
  kappa_model : ∀ I : CochainComplex X.modules ℤ,
    lk.eta.app I ≫
      (conjugateIsoEquiv lk.edge.derivedAdjunction
        (lg.edge.derivedAdjunction.comp lf.edge.derivedAdjunction)
        pullback.symm).hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary_right.hom (ComplexShape.up ℤ)).app I) ≫
        lg.eta.app ((lf.edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          lg.edge.right.map (lf.eta.app I)
  tensor : ∀ U V : Z.D,
    pullback.hom.app (Z.closed.tensor.obj (U, V)) ≫
      lf.edge.left.map (lg.tensor U V).hom ≫
      (lf.tensor (lg.edge.left.obj U) (lg.edge.left.obj V)).hom =
    (lk.tensor U V).hom ≫
      X.closed.tensor.map
        (X := (lk.edge.left.obj U, lk.edge.left.obj V))
        (Y := (lf.edge.left.obj (lg.edge.left.obj U), lf.edge.left.obj (lg.edge.left.obj V)))
        (pullback.hom.app U, pullback.hom.app V)
  unit : pullback.hom.app Z.closed.monoidal.tensorUnit ≫
      lf.edge.left.map lg.unit.hom ≫ lf.unit.hom = lk.unit.hom

/-- The scalar-association pullback comparison and the normalized right-derived
composition comparison respect tensor, unit and the canonical Hom bijections.
Source: Stacks Project, Modules on Sites, Tags 03D7, 03D8 and 03EL;
Cohomology on Sites, Tags 0D6D, 0D6E, 07A6 and 0FPI.
(blueprint: lem-sfb-ringed-derived-composition-comparison).

Proof:
1. The geometric path isomorphism and structural ring-map equality identify
ordinary scalar extensions. On inserted generators the ordinary comparison is
one tensor x mapped to one tensor (one tensor x). Scalar multiplication extends
this to an invertible module map. The normalized underlying Hom bijections show
that its right mate is the supplied ordinary direct-image comparison. This gives
ordinary, ordinary_insertion, ordinary_right and ordinary_mate.
2. Both ordinary pullbacks preserve flat-term K-flat complexes. Hence the
ordinary comparison localizes to a unique left-derived isomorphism c, with
pullback_model. The signed cochain tensor-composition identity localizes to the
tensor equation; representatives and naturality give it for all derived objects.
On the coefficient unit both paths multiply by the same structural scalar,
giving the unit equation.
3. Use the adjunction mate of c as kappa. Right-derived composition is computed
on a K-injective I by a K-injective resolution j of f_*I. The map g_*j is a
quasi-isomorphism by the resolving-adjoint
acyclicity argument; f_*I need not be K-injective. The universal right-derived
comparison has the representative formula in kappa_model at every complex,
by naturality and the derived universal property.
4. For a flat-term K-flat P and K-injective I, use the two canonical inverse Hom
formulas. Naturality of the ordinary g-counit moves j across the transpose.
The two alpha comparisons and c identify the resulting map with Q of the ordinary
scalar-association transpose, which is the ordinary composite-adjunction formula
of step 1. A right fraction followed by a K-flat resolution represents every
morphism from QN; naturality therefore gives equality of the corresponding Hom bijections for
arbitrary sources. Every target has a K-injective representative, so naturality
also gives the equation at arbitrary targets. This identifies the universal
right-derived comparison with the adjunction mate of c and proves kappa_model.
This result concerns only composition; it asserts neither identity nor geometric
2-isomorphism normalization and does not assert existence of monoidal lifts. -/
theorem compositionCore_exists {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse)
    (hθ : k.ringMap = θ.hom.app
      ((sheafCompose Z.J (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
      f.inverse.map g.ringMap ≫ f.ringMap) :
    Nonempty (CompositionCore lf lg lk θ) := by sorry

end CategoryTheory.RingedDerivedComparisons
