/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.OpenTensorNormalization
public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.ScalarSixExceptional
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Compactification scalar maps and exceptional scalar transposes

Source: blueprint latest, sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md,
coefficient paragraph; sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.md and det-prop-scalar-six-exceptional.md.
(blueprint: def-sf-condensed-scalar-shriek-mates).

The compact-support map is the existing `scalarCompactSupportMap`, defined on all ambient
objects without an invertibility hypothesis. The new transpose uses supplied adjunctions
on arbitrary full subcategories. Only its specified compact-support component is inverted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedScalarShriekMates

/-- The geometric construction domain: a listed condensed coefficient map and a chosen
compactification of a separated finite-type morphism between finite-type schemes over the
fixed algebraic closure of a finite field. The structure morphisms of `X` and `Y` need not
be separated. Source: coefficient paragraph and displayed scalar formulas
(blueprint: def-sf-condensed-scalar-shriek-mates). -/
structure Geometry where
  field : WeilConjectures.FiniteFieldDatum.{u}
  ell : ℕ
  [prime : Fact ell.Prime]
  different : ell ≠ ringChar field.k
  Λ : ScalarSixRing.{u}
  Λ' : ScalarSixRing.{u}
  a : Λ ⟶ Λ'
  listed : ListedCoefficientMap ell a
  X : Over (Spec (CommRingCat.of field.k))
  Y : Over (Spec (CommRingCat.of field.k))
  [sourceFiniteType : LocallyOfFiniteType X.hom]
  [sourceQuasiCompact : QuasiCompact X.hom]
  [targetFiniteType : LocallyOfFiniteType Y.hom]
  [targetQuasiCompact : QuasiCompact Y.hom]
  f : X ⟶ Y
  [separated : IsSeparated f.left]
  [finiteType : LocallyOfFiniteType f.left]
  [quasiCompact : QuasiCompact f.left]
  compactification : Compactification.BoundaryCompactification f.left

/-- The displayed compactification scalar map, specialized from the existing ambient
construction. Its component at every ambient `K` is the direct-image counit mate at `j_!K`
followed by `Rp_*` of the unit-normalized open scalar comparison. This definition asserts
neither invertibility nor compactification independence.
Source: compact-support displayed formula and coefficient paragraph
(blueprint: def-sf-condensed-scalar-shriek-mates). -/
abbrev compactificationScalarMap (g : Geometry.{u}) :=
  scalarCompactSupportMap g.a g.compactification.obj.obj.i g.compactification.obj.obj.g

/-- Four arbitrary full subcategories together with precisely the membership conditions
needed to restrict the two compactification functors and the two scalar functors. They may
be the constructible finite-Tor subcategories or localizing hulls; no such particular choice
or stability theorem is assumed. Source: construction-domain paragraph
(blueprint: def-sf-condensed-scalar-shriek-mates). -/
structure Domains (g : Geometry.{u}) where
  source : ObjectProperty
    (DerivedCategory (ModuleRingedComparison.internalModules g.Λ.X g.X.left))
  target : ObjectProperty
    (DerivedCategory (ModuleRingedComparison.internalModules g.Λ.X g.Y.left))
  source' : ObjectProperty
    (DerivedCategory (ModuleRingedComparison.internalModules g.Λ'.X g.X.left))
  target' : ObjectProperty
    (DerivedCategory (ModuleRingedComparison.internalModules g.Λ'.X g.Y.left))
  lower_mem : ∀ K : source.FullSubcategory,
    target ((rightDerivedLowerShriekOfCompactification g.Λ.X
      g.compactification.obj.obj).obj K.obj)
  lower_mem' : ∀ K : source'.FullSubcategory,
    target' ((rightDerivedLowerShriekOfCompactification g.Λ'.X
      g.compactification.obj.obj).obj K.obj)
  scalar_source_mem : ∀ K : source.FullSubcategory,
    source' ((scalarSixChange g.a g.X.left).obj K.obj)
  scalar_target_mem : ∀ N : target.FullSubcategory,
    target' ((scalarSixChange g.a g.Y.left).obj N.obj)

/-- The given compactification functor restricted to the chosen full subcategories.
Source: construction-domain paragraph (blueprint: def-sf-condensed-scalar-shriek-mates). -/
def Domains.lower {g : Geometry.{u}} (d : Domains g) :
    d.source.FullSubcategory ⥤ d.target.FullSubcategory :=
  d.target.lift (d.source.ι ⋙ rightDerivedLowerShriekOfCompactification g.Λ.X
    g.compactification.obj.obj) d.lower_mem

/-- The same compactification functor at the new coefficients, restricted to its domain.
Source: construction-domain paragraph (blueprint: def-sf-condensed-scalar-shriek-mates). -/
def Domains.lower' {g : Geometry.{u}} (d : Domains g) :
    d.source'.FullSubcategory ⥤ d.target'.FullSubcategory :=
  d.target'.lift (d.source'.ι ⋙ rightDerivedLowerShriekOfCompactification g.Λ'.X
    g.compactification.obj.obj) d.lower_mem'

/-- Actual ordinary derived scalar extension on the chosen source subcategory.
Source: construction-domain paragraph (blueprint: def-sf-condensed-scalar-shriek-mates). -/
def Domains.scalarSource {g : Geometry.{u}} (d : Domains g) :
    d.source.FullSubcategory ⥤ d.source'.FullSubcategory :=
  d.source'.lift (d.source.ι ⋙ scalarSixChange g.a g.X.left) d.scalar_source_mem

/-- Actual ordinary derived scalar extension on the chosen target subcategory.
Source: construction-domain paragraph (blueprint: def-sf-condensed-scalar-shriek-mates). -/
def Domains.scalarTarget {g : Geometry.{u}} (d : Domains g) :
    d.target.FullSubcategory ⥤ d.target'.FullSubcategory :=
  d.target'.lift (d.target.ι ⋙ scalarSixChange g.a g.Y.left) d.scalar_target_mem

/-- The exceptional scalar comparison at `N`, on its stated construction domain. Transpose
`gamma⁻¹ ≫ S_Y(epsilon_N)` under the supplied new-coefficient adjunction. Here `gamma` is
exactly the existing ambient compactification scalar map. The supplied old adjunction
provides the counit. The defining hom-set equivalence fixes the counit equation
`F'(beta) ≫ epsilon' = gamma⁻¹ ≫ S_Y(epsilon)` by `Adjunction.homEquiv_symm_apply`;
no exceptional existence, invertibility of beta, or independence is asserted.
Source: exceptional displayed transpose and counit equation; coefficient paragraph
(blueprint: def-sf-condensed-scalar-shriek-mates). -/
def exceptionalScalarTranspose {g : Geometry.{u}} (d : Domains g)
    (G : d.target.FullSubcategory ⥤ d.source.FullSubcategory) (adj : d.lower ⊣ G)
    (G' : d.target'.FullSubcategory ⥤ d.source'.FullSubcategory) (adj' : d.lower' ⊣ G')
    (N : d.target.FullSubcategory)
    [IsIso ((compactificationScalarMap g).app (G.obj N).obj)] :
    d.scalarSource.obj (G.obj N) ⟶ G'.obj (d.scalarTarget.obj N) :=
  (adj'.homEquiv _ _) (ObjectProperty.homMk
    (inv ((compactificationScalarMap g).app (G.obj N).obj) ≫
      (scalarSixChange g.a g.Y.left).map (adj.counit.app N).hom))

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedScalarShriekMates
