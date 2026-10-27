/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.KummerPartialNerveMorphism
public import Sheaf.Paper.TameRootTowerExtension
public import Sheaf.Paper.PartialKummerBoundaryUnitModel
public import Sheaf.CategoryTheory.CondensedProductBarComparison
public import Sheaf.Paper.KummerParameterizedTerm
public import Sheaf.Paper.KummerNerveCoordinates
public import Sheaf.Paper.KummerChartGeometryMaps
public import Sheaf.Paper.KummerNormalizedChart
public import Sheaf.Paper.KummerRefinement
public import Sheaf.Paper.KummerCoefficientModels


/-! # Compatible finite-field and algebraic-closure Kummer arrows

Source: main-20261015 direct-images proof paragraph (3), extracted argument.
Exact all-continuous geometric reference WANTED.
(blueprint: def-sfb-kummer-partial-nerve-scalar-morphism).

## Main definitions

* `MorphismData`: the same continuous E-matrix and actual ordinary scalar-extension squares.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.KummerPartialNerve
open Profinite.CondensedAction
section Morphisms
variable {p : ℕ} {Y : Scheme.{u}} {A : Type u} [Finite A] [DecidableEq A]
  {C : A → Y.IdealSheafData} {J Jo Ji : Finset A}

/-- Ordinary scalar compatibility of two actual extension arrows over fixed rings.
The puncture isomorphisms use the canonical inverse-image/scalar coherence.
Source: direct-image proof (3), simultaneous finite-coefficient scalar extension
(blueprint: def-sfb-kummer-partial-nerve-scalar-morphism). -/
structure ScalarCompatibility (R S : CategoryTheory.CondensedBar.Ring.{u}) (a : R ⟶ S)
    {V T W : Scheme.{u}} (j : V ⟶ T) (d : V ⟶ W)
    (L L' : PartialKummer.SchemeModules R.X W)
    (N N' : PartialKummer.SchemeModules R.X T)
    (O O' : PartialKummer.SchemeModules S.X T)
    (r : (CondensedRing.upperStar R.X j).obj N ≅
      (CondensedRing.upperStar R.X d).obj L)
    (r' : (CondensedRing.upperStar R.X j).obj N' ≅
      (CondensedRing.upperStar R.X d).obj L')
    (s : (CondensedRing.upperStar S.X j).obj O ≅
      (CondensedRing.upperStar S.X d).obj
        ((extendCoefficients R S a W).obj L))
    (s' : (CondensedRing.upperStar S.X j).obj O' ≅
      (CondensedRing.upperStar S.X d).obj
        ((extendCoefficients R S a W).obj L'))
    (f : N ⟶ N') (g : O ⟶ O') where
  scalar : (extendCoefficients R S a T).obj N ≅ O
  scalar' : (extendCoefficients R S a T).obj N' ≅ O'
  scalar_puncture : (CondensedRing.upperStar S.X j).mapIso scalar ≪≫ s =
    scalarPunctureIso R S a j d N L r
  scalar_puncture' : (CondensedRing.upperStar S.X j).mapIso scalar' ≪≫ s' =
    scalarPunctureIso R S a j d N' L' r'
  scalar_map : (extendCoefficients R S a T).map f ≫ scalar'.hom =
    scalar.hom ≫ g

/-- The actual extended morphism, its finite matrix, scalar extension and derived
naturality squares, with both coefficient models fixed before stating the equations.
Source: direct-image proof (3), actual puncture morphisms
(blueprint: def-sfb-kummer-partial-nerve-scalar-morphism). -/
structure MorphismData (D : Y.IdealSheafData) (c : TameRootExtensionChart C J)
    (split : DeckSplit p Jo Ji J) (g : TameRootChartGeometry p D c)
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (L L' : PartialKummer.SchemeModules (fieldRing E.1).X (tameBoundaryOpen D).toScheme)
    (f : L ⟶ L') (i : c.boundary ⟶ c.tower p)
    (hi : i ≫ c.towerMap p = c.boundaryToBase)
    [eE : Environment (fieldRing E.1)
      (ParameterRootDeckGroup p {a : A // a ∈ Jo})
      (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
    [eO : Environment (fieldRing (PadicAlgCl ℓ))
      (ParameterRootDeckGroup p {a : A // a ∈ Jo})
      (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
    {M M' : PartialKummer.FiniteRepresentation E.1
      (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
        ParameterRootDeckGroup p {a : A // a ∈ Ji})}
    (finite : FieldChart D c split g M E.1 (RingHom.id E.1) L i hi)
    (finite' : FieldChart D c split g M' E.1 (RingHom.id E.1) L' i hi)
    (closure : FieldChart D c split g M (PadicAlgCl ℓ) E.1.subtype
      ((extendToClosure ℓ E _).obj L) i hi)
    (closure' : FieldChart D c split g M' (PadicAlgCl ℓ) E.1.subtype
      ((extendToClosure ℓ E _).obj L') i hi) where
  finiteMap : CoefficientMorphism D c split g finite finite' f
  closureMap : CoefficientMorphism D c split g closure closure'
    ((extendToClosure ℓ E (tameBoundaryOpen D).toScheme).map f)
  uniqueE : UniqueLisseExtensions (fieldRing E.1) (c.openInclusion p D)
  uniqueOmega : UniqueLisseExtensions (fieldRing (PadicAlgCl ℓ)) (c.openInclusion p D)
  matrix : (Fin M.rank → E.1) →ₗ[E.1] (Fin M'.rank → E.1)
  matrix_continuous : Continuous matrix
  matrix_equivariant : ∀ g x,
    matrix (M.action g x) = M'.action g (matrix x)
  matrixE : PartialKummer.HasMatrix finite.data.condensation finite'.data.condensation
    matrix finiteMap.boundaryMap
  matrixOmega : PartialKummer.HasMatrix closure.data.condensation closure'.data.condensation
    matrix closureMap.boundaryMap
  scalars : ScalarCompatibility (fieldRing E.1) (fieldRing (PadicAlgCl ℓ))
    (CondensedRing.kummerCoefficientMap ℓ E) (c.openInclusion p D) (c.toOpen p D)
    L L' finite.data.root.extension finite'.data.root.extension
    closure.data.root.extension closure'.data.root.extension
    finite.data.root.restriction finite'.data.root.restriction
    closure.data.root.restriction closure'.data.root.restriction
    finiteMap.extensionMap closureMap.extensionMap

end Morphisms

end AlgebraicGeometry.ProEtale.KummerPartialNerve
