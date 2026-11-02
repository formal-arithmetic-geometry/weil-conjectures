/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-source-comparisons). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- Canonical source comparison on the literal Cartesian square, using the
root-normalized Tate pullback and derived tensorator.
Source: base-change clause (blueprint: def-pur-transport-source-comparisons). -/
def sourceBaseChange (c : Coefficient ell) {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (v : Y' ⟶ Y) (d : ℕ)
    (p : LinePullCoordinates ell c (pullback.fst f v)) (K : c.derived ell Y) :
    (CondensedRing.upperStar (c.obj ell) (pullback.fst f v)).leftDerivedFunctor.obj
        ((c.smoothSource ell f d).obj K) ≅
      (c.smoothSource ell (pullback.snd f v) d).obj
        ((CondensedRing.upperStar (c.obj ell) v).leftDerivedFunctor.obj K) :=
  (Functor.Monoidal.μIso
    (CondensedRing.upperStar (c.obj ell) (pullback.fst f v)).leftDerivedFunctor
    _ _).symm ≪≫
  tensorIso ((CondensedRing.pullbackSquareComparison (c.obj ell)
    (CommSq.mk (pullback.condition (f := f) (g := v)))).symm.app K)
    (p.derived ell d)

/-- Canonical source compositor: pullback composition, even-shift concatenation,
Tate symmetry, associativity, Tate pullback, and the inverse-image tensorator.
The symmetry is the named Koszul braiding `DerivedCategory.braidedCategory'` of the
derived tensor, not a braiding selected from a `Nonempty` witness.
Source: composition clause (blueprint: def-pur-transport-source-comparisons). -/
def sourceComp (c : Coefficient ell) {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (ell : X.residueField x)]
    (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ)
    (p : LinePullCoordinates ell c f) (K : c.derived ell Z) :
    (c.smoothSource ell (f ≫ g) (d + e)).obj K ≅
      (c.smoothSource ell f d).obj ((c.smoothSource ell g e).obj K) :=
  letI := _root_.DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X))
  tensorIso ((CondensedRing.leftDerivedUpperStarComp (c.obj ell) f g).app K)
    ((derivedProduct ell c X d e).symm ≪≫ β_ _ _) ≪≫
  (α_ _ _ _).symm ≪≫
  tensorIso
    (tensorIso (Iso.refl _) (p.derived ell e).symm ≪≫
      Functor.Monoidal.μIso (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor _ _)
    (Iso.refl _)

/-- The proper/open composition model is the actual composite compactification.
Source: compact-support composition (blueprint: def-pur-transport-source-comparisons). -/
def compositeCompactification {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (cf.g ≫ cg.i)) :
    Compactification (f ≫ g) where
  Z := cr.obj.obj.Z
  i := cf.i ≫ cr.obj.obj.i
  g := cr.obj.obj.g ≫ cg.g
  isProper := inferInstance
  isOpenImmersion := inferInstance
  comm := calc
    f ≫ g = (cf.i ≫ cf.g) ≫ g := congrArg (· ≫ g) cf.comm
    _ = cf.i ≫ ((cf.g ≫ cg.i) ≫ cg.g) :=
      (congrArg (fun h ↦ (cf.i ≫ cf.g) ≫ h) cg.comm).trans (by simp)
    _ = cf.i ≫ ((cr.obj.obj.i ≫ cr.obj.obj.g) ≫ cg.g) :=
      congrArg (fun h ↦ cf.i ≫ (h ≫ cg.g)) cr.obj.obj.comm
    _ = (cf.i ≫ cr.obj.obj.i) ≫ (cr.obj.obj.g ≫ cg.g) := by simp

end AlgebraicGeometry.ProEtale.PurityTransport
