/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.TransportLinePull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Canonical pullback and dual-Tate operation helpers

Source: latest blueprint, thm-a1-curve-perverse-heart.proof.md, Step 2
(blueprint: def-per-condensed-lisse-dual-operations).
These are concrete operation formulas; no geometric invertibility is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u c₁ v b w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseDual

variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

/-- The object of the existing coefficient presentation. The main theorem uses
`.closure`, the finite-subextension-valued coefficient, not the full continuous ring.
Source: Step 2, coefficient convention
(blueprint: def-per-condensed-lisse-dual-operations). -/
abbrev coefficients :=
  c.obj.{u} ell

/-- The existing module-object category over the pulled-back coefficient ring.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
abbrev Modules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (c.obj ell) T)

/-- The ordinary unbounded module-object derived category.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
abbrev D (T : Scheme.{u}) := DerivedCategory (Modules ell c T)

/-- Ordinary coefficient dual followed by tensor with a fixed line, written
with abstract endpoints to retain the existing closed structure opaquely.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
def dualTensorFunctor {C : Type c₁} [Category.{v} C] [MonoidalCategory C]
    [MonoidalClosed C] (L : C) : Cᵒᵖ ⥤ C :=
  MonoidalClosed.internalHom.flip.obj (𝟙_ C) ⋙ tensorRight L

/-- The ordinary closed-functor comparison with a line. The first factor is
specified by evaluation; the second is the supplied line-pullback morphism.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
def dualTensorPull {C : Type c₁} [Category.{v} C] [MonoidalCategory C]
    [MonoidalClosed C] {B : Type b} [Category.{w} B] [MonoidalCategory B]
    [MonoidalClosed B] (F : C ⥤ B) [F.Monoidal]
    (L : C) (L' : B) (e : F.obj L ⟶ L') (M : C) :
    F.obj ((dualTensorFunctor L).obj (op M)) ⟶
      (dualTensorFunctor L').obj (op (F.obj M)) :=
  (Functor.Monoidal.μIso F ((ihom M).obj (𝟙_ C)) L).inv ≫
    tensorHom
      ((Functor.LaxMonoidal.ihomComparison F M).natTrans.app (𝟙_ C) ≫
        (ihom (F.obj M)).map (Functor.Monoidal.εIso F).inv) e

/-- Coefficient-parametric ordinary dual and Tate line. Keeping the existing
coefficient abstract avoids expanding its module-category instance data.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
def coefficientLinearDual (c : PurityTransport.Coefficient ell) (T : Scheme.{u})
    (d : ℕ) :=
  dualTensorFunctor (c.line ell T d)

/-- The finite-rank linear dual followed by the positive Tate twist. This is
ordinary sheaf internal Hom and ordinary tensor, not derived Hom of a sheaf.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
abbrev linearDualTwist (T : Scheme.{u}) (d : ℕ) :
    (Modules ell c T)ᵒᵖ ⥤ Modules ell c T :=
  coefficientLinearDual ell c T d

/-- Canonical derived inverse image: exact module inverse image localized termwise.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
def pull {V T : Scheme.{u}} (j : V ⟶ T) :=
  (CondensedRing.upperStar (c.obj ell) j).mapDerivedCategory

/-- The monoidal structure on exact derived pullback is transported from its
canonical total-derived comparison. Source: Step 2
(blueprint: def-per-condensed-lisse-dual-operations). -/
instance pullMonoidal {V T : Scheme.{u}} (j : V ⟶ T) : (pull ell c j).Monoidal :=
  Functor.Monoidal.transport
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) j)

/-- The composition comparison on the exact derived inverse images.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
def pullComp {W V T : Scheme.{u}} (i : W ⟶ V) (j : V ⟶ T) :
    pull ell c (i ≫ j) ≅ pull ell c j ⋙ pull ell c i :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp (c.obj ell) i j) ≪≫
    Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar (c.obj ell) j)
      (CondensedRing.upperStar (c.obj ell) i)

/-- The ordinary closed-functor pullback map, constructed while the coefficient
is abstract. Its line map is precisely the existing root-normalized coordinate.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
def coefficientLinearPull (c : PurityTransport.Coefficient ell) {V T : Scheme.{u}}
    (j : V ⟶ T) (q : PurityTransport.LinePullCoordinates ell c j)
    (d : ℕ) (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (c.obj ell) T)) :
    (CondensedRing.upperStar (c.obj ell) j).obj
        ((coefficientLinearDual ell c T d).obj (op L)) ⟶
      (coefficientLinearDual ell c V d).obj
        (op ((CondensedRing.upperStar (c.obj ell) j).obj L)) :=
  dualTensorPull (CondensedRing.upperStar (c.obj ell) j)
    (c.line ell T d) (c.line ell V d) (q.power d).hom L

/-- Ordinary inverse image of a dual-and-twist, compared using evaluation,
the unit tensorator, and the normalized root-line pullback. This fixes the
cohomology square for automorphisms, including geometric Frobenius.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
def linearPullMap {V T : Scheme.{u}} (j : V ⟶ T)
    (q : PurityTransport.LinePullCoordinates ell c j)
    (d : ℕ) (L : Modules ell c T) :=
  coefficientLinearPull ell c j q d L

/-- The derived/homology comparison of exact inverse image, with its published
normalization on representing complexes. Explicit endpoints keep its concrete
construction from unfolding while forming the compatibility square.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
def cohomPull {V T : Scheme.{u}} (j : V ⟶ T) (n : ℤ) :
    DerivedCategory.homologyFunctor (Modules ell c T) n ⋙
        CondensedRing.upperStar (c.obj ell) j ≅
      pull ell c j ⋙ DerivedCategory.homologyFunctor (Modules ell c V) n :=
  (CondensedRing.upperStar (c.obj ell) j).mapDerivedCategoryHomologyFunctorIso n

/-- The inverse exact-inverse-image cohomology map, with its two objects
specified directly rather than as evaluations of composite functors.
Source: Step 2 (blueprint: def-per-condensed-lisse-dual-operations). -/
def cohomPullBack {V T : Scheme.{u}} (j : V ⟶ T) (n : ℤ) (M : D ell c T) :
    (DerivedCategory.homologyFunctor (Modules ell c V) n).obj ((pull ell c j).obj M) ⟶
      (CondensedRing.upperStar (c.obj ell) j).obj
        ((DerivedCategory.homologyFunctor (Modules ell c T) n).obj M) :=
  (cohomPull ell c j n).inv.app M

end AlgebraicGeometry.ProEtale.CondensedLisseDual
