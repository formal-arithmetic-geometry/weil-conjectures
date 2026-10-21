/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerNerveTransport

/-! # Constant-extension identifications on the actual Kummer nerve
Source: direct-image proof (3), root ratios and extension restriction.
(blueprint: def-sfb-kummer-constant-nerve-term).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar
variable (A : Ring.{u})

/-- Canonical pullback comparison for a commuting square and a constant module.
Source: direct-image proof (3), actual covering-nerve restriction
(blueprint: def-sfb-kummer-constant-nerve-term). -/
def kummerSquareModuleComposite {V W Z N : Scheme.{u}}
    (θ : Z ⟶ N) (q : N ⟶ W) (π : Z ⟶ V) (v : V ⟶ W)
    (h : θ ≫ q = π ≫ v) (L : KummerModules A.X W) (M : Modules A)
    (e : (upperStar A.X v).obj L ≅ ((upperStarFromPoint V).mapMod A.X).obj M) :
    (upperStar A.X θ).obj ((upperStar A.X q).obj L) ≅
      ((upperStarFromPoint Z).mapMod A.X).obj M := by
  let e₁ : (upperStar A.X θ).obj ((upperStar A.X q).obj L) ≅
      (upperStar A.X (θ ≫ q)).obj L := ((upperStarComp A.X θ q).app L).symm
  let e₂ : (upperStar A.X (θ ≫ q)).obj L ≅
      (upperStar A.X (π ≫ v)).obj L := (upperStarCongr A.X h).app L
  let e₃ : (upperStar A.X (π ≫ v)).obj L ≅
      (upperStar A.X π).obj ((upperStar A.X v).obj L) :=
    (upperStarComp A.X π v).app L
  let e₄ : (upperStar A.X π).obj ((upperStar A.X v).obj L) ≅
      (upperStar A.X π).obj (((upperStarFromPoint V).mapMod A.X).obj M) :=
    (upperStar A.X π).mapIso e
  let e₅ : (upperStar A.X π).obj (((upperStarFromPoint V).mapMod A.X).obj M) ≅
      ((upperStarFromPoint Z).mapMod A.X).obj M :=
    (fromCondensedPullbackIso A.X π).app M
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅

/-- The commuting-square comparison is uniquely fixed by its canonical component.
Source: direct-image proof (3), exact pullback composition
(blueprint: def-sfb-kummer-constant-nerve-term).
Proof: the canonical composite supplies the isomorphism; equality of hom components
implies equality of isomorphisms. -/
theorem kummerSquareModuleIso_existsUnique {V W Z N : Scheme.{u}}
    (θ : Z ⟶ N) (q : N ⟶ W) (π : Z ⟶ V) (v : V ⟶ W)
    (h : θ ≫ q = π ≫ v) (L : KummerModules A.X W) (M : Modules A)
    (e : (upperStar A.X v).obj L ≅ ((upperStarFromPoint V).mapMod A.X).obj M) :
    ∃! b : (upperStar A.X θ).obj ((upperStar A.X q).obj L) ≅
      ((upperStarFromPoint Z).mapMod A.X).obj M,
      b.hom = (kummerSquareModuleComposite A θ q π v h L M e).hom := by
  sorry

/-- The uniquely normalized square comparison, preserving its canonical component.
Source: direct-image proof (3), exact pullback composition
(blueprint: def-sfb-kummer-constant-nerve-term). -/
def kummerSquareModuleIso {V W Z N : Scheme.{u}}
    (θ : Z ⟶ N) (q : N ⟶ W) (π : Z ⟶ V) (v : V ⟶ W)
    (h : θ ≫ q = π ≫ v) (L : KummerModules A.X W) (M : Modules A)
    (e : (upperStar A.X v).obj L ≅ ((upperStarFromPoint V).mapMod A.X).obj M) :
    (upperStar A.X θ).obj ((upperStar A.X q).obj L) ≅
      ((upperStarFromPoint Z).mapMod A.X).obj M :=
  (kummerSquareModuleIso_existsUnique A θ q π v h L M e).choose

/-- Derived exact point pullback sends a degree-zero module to its actual sheaf in
zero degree. Source: direct-image proof (3), constant extension
(blueprint: def-sfb-kummer-constant-nerve-term). -/
def kummerPointSingle (X : Scheme.{u}) (M : Modules A) :=
  (((upperStarFromPoint X).mapMod A.X).mapDerivedCategorySingleFunctor 0).app M


/-- The exact degree-zero square comparison, using the actual point comparison.
Source: direct-image proof (3), restriction of the constant extension
(blueprint: def-sfb-kummer-constant-nerve-term). -/
def kummerSquareDerivedModuleComposite {V W Z N Z' : Scheme.{u}}
    (θ : Z ⟶ N) (q : N ⟶ W) (π : Z ⟶ V) (v : V ⟶ W)
    (h : θ ≫ q = π ≫ v) (L : KummerModules A.X W) (M : Modules A)
    (e : (upperStar A.X v).obj L ≅ ((upperStarFromPoint V).mapMod A.X).obj M)
    (f : Z ⟶ Z') :
    (upperStar A.X θ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj ((upperStar A.X q).obj L)) ≅
    (upperStar A.X f).mapDerivedCategory.obj
      ((derivedFromCondensed A.X Z').obj ((DerivedCategory.singleFunctor _ 0).obj M)) :=
  kummerPullSingle A.X θ _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (kummerSquareModuleIso A θ q π v h L M e) ≪≫
    (kummerPointSingle A Z M).symm ≪≫
    ((derivedFromCondensedPullbackIso A.X f).app
      ((DerivedCategory.singleFunctor _ 0).obj M)).symm

/-- The derived comparison is uniquely fixed by the actual degree-zero composite.
Source: direct-image proof (3), exact constant-extension comparisons
(blueprint: def-sfb-kummer-constant-nerve-term).
Proof: the displayed composite is an isomorphism, since every factor is an
isomorphism. Equality of its hom component fixes the isomorphism uniquely. -/
theorem kummerSquareDerivedModuleIso_existsUnique {V W Z N Z' : Scheme.{u}}
    (θ : Z ⟶ N) (q : N ⟶ W) (π : Z ⟶ V) (v : V ⟶ W)
    (h : θ ≫ q = π ≫ v) (L : KummerModules A.X W) (M : Modules A)
    (e : (upperStar A.X v).obj L ≅ ((upperStarFromPoint V).mapMod A.X).obj M)
    (f : Z ⟶ Z') :
    ∃! b : (upperStar A.X θ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj ((upperStar A.X q).obj L)) ≅
    (upperStar A.X f).mapDerivedCategory.obj
      ((derivedFromCondensed A.X Z').obj ((DerivedCategory.singleFunctor _ 0).obj M)),
      b.hom = (kummerSquareDerivedModuleComposite A θ q π v h L M e f).hom := by
  sorry

/-- The uniquely component-normalized derived constant-extension comparison.
Source: direct-image proof (3), exact constant extension
(blueprint: def-sfb-kummer-constant-nerve-term). -/
def kummerSquareDerivedModuleIso {V W Z N Z' : Scheme.{u}}
    (θ : Z ⟶ N) (q : N ⟶ W) (π : Z ⟶ V) (v : V ⟶ W)
    (h : θ ≫ q = π ≫ v) (L : KummerModules A.X W) (M : Modules A)
    (e : (upperStar A.X v).obj L ≅ ((upperStarFromPoint V).mapMod A.X).obj M)
    (f : Z ⟶ Z') :
    (upperStar A.X θ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj ((upperStar A.X q).obj L)) ≅
    (upperStar A.X f).mapDerivedCategory.obj
      ((derivedFromCondensed A.X Z').obj ((DerivedCategory.singleFunctor _ 0).obj M)) :=
  (kummerSquareDerivedModuleIso_existsUnique A θ q π v h L M e f).choose

/-- Equality of the actual parameter projection maps, before any derived functor.
Source: direct-image proof (3), restriction of root coordinates
(blueprint: def-sfb-kummer-constant-nerve-term).
Proof: the parameter-projection naturality square gives projection followed by j.
Compose with q and substitute j q = v a; associativity gives the displayed map. -/
theorem kummerPuncturedParameter_over {V T W U : Scheme.{u}}
    (j : V ⟶ T) (q : T ⟶ U) (v : V ⟶ W) (a : W ⟶ U)
    (h : j ≫ q = v ≫ a) (P : Profinite.{u}) :
    coefficientParameterMap j P ≫ coefficientParameterProjection T P ≫ q =
      coefficientParameterProjection V P ≫ v ≫ a := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
