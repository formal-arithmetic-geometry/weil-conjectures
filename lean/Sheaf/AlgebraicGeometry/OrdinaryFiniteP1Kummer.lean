/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison

/-!
# Canonical arrows for the ordinary finite projective-line calculation

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-amb-p1-decomposition.md and
thm-amb-p1-adjunction.md; Stacks Project, Tags 03PL and 03FD
(blueprint: def-asd-ordinary-finite-p1-kummer-class).

## Main definitions

* `ordinaryFiniteRootMap`: scalar extension of roots of unity.
* `ordinaryFiniteClass`: realization of a module-derived class in abelian cohomology.
* `ordinaryFiniteP1KummerClass`: the scalar Kummer class of the specified `O(1)`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor ChangeOfRings

namespace AlgebraicGeometry.Etale

/-- The constant coefficient sheaf, in the existing finite-twist encoding.
Source: blueprint thm-amb-p1-decomposition
(blueprint: def-asd-ordinary-finite-p1-kummer-class). -/
abbrev ordinaryFiniteConstant (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- The map from the integral constant sheaf sending one to one.
Source: Stacks, Tag 03FD (blueprint: def-asd-ordinary-finite-p1-kummer-class). -/
def ordinaryFiniteIntegralGenerator (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (RawModuleScalarComparison.forget A T).obj (ordinaryFiniteConstant A T) :=
  ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv _ _).symm
    (AddCommGrpCat.ofHom
      ((((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
            (op (Scheme.Etale.mk (𝟙 T))))).hom).comp
        ((Int.castAddHom A).comp AddEquiv.ulift.toAddMonoidHom)))

/-- View a derived module class as an abelian cohomology class, by forgetting its Ext
class and precomposing with the integral generator. This is a map, not a chosen
cohomology equivalence.
Source: Stacks, Tag 03FD (blueprint: def-asd-ordinary-finite-p1-kummer-class). -/
@[irreducible]
def ordinaryFiniteClass (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ)
    (c : (DerivedCategory.singleFunctor _ 0).obj (ordinaryFiniteConstant A T) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj F)⟦(n : ℤ)⟧) :
    Sheaf.H ((RawModuleScalarComparison.forget A T).obj F) n :=
  (Ext.mk₀ (ordinaryFiniteIntegralGenerator A T)).comp
    ((Ext.homEquiv.symm c).mapExactFunctor (RawModuleScalarComparison.forget A T)) (zero_add n)

/-- The canonical scalar map on roots of unity, `z ↦ 1 ⊗ z`, on sections.
Source: Stacks, Tag 03PK (blueprint: def-asd-ordinary-finite-p1-kummer-class). -/
def ordinaryFiniteRootGenerator (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (W : T.Etaleᵒᵖ) :
    (T.rootsOfUnitySheaf N).obj.obj W →+
      ((RawModuleScalarComparison.forget A T).obj
        (Scheme.finiteEtaleTateLine T N A hA)).obj.obj W :=
  ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
      ((toSheafify T.smallEtaleTopology
        (Scheme.finiteEtaleMuModulePresheaf T N ⋙
          ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA))).app W)).hom.comp
    (((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}).map
      ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
        (Scheme.finiteEtaleTwistScalar N A hA)).unit.app
        (Scheme.finiteEtaleMuModuleObj T N W))).hom)

/-- Naturality of the scalar map `z ↦ 1 ⊗ z`.
Source: Stacks, Tag 03PK (blueprint: def-asd-ordinary-finite-p1-kummer-class).
Proof: the scalar-extension unit is natural and the sheafification unit is natural;
compose their two squares. Their underlying maps are the displayed section maps. -/
theorem ordinaryFiniteRootGenerator_naturality (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    {W V : T.Etaleᵒᵖ} (f : W ⟶ V) :
    (T.rootsOfUnitySheaf N).obj.map f ≫
        AddCommGrpCat.ofHom (ordinaryFiniteRootGenerator A N hA T V) =
      AddCommGrpCat.ofHom (ordinaryFiniteRootGenerator A N hA T W) ≫
        ((RawModuleScalarComparison.forget A T).obj
          (Scheme.finiteEtaleTateLine T N A hA)).obj.map f := by
  let r := Scheme.finiteEtaleTwistScalar N A hA
  let F := Scheme.finiteEtaleMuModulePresheaf T N
  let U := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
  let U₀ := forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}
  let η := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} r).unit
  let σ := toSheafify T.smallEtaleTopology (F ⋙ ModuleCat.extendScalars r)
  have hη := congrArg (fun g ↦ U₀.map g) (η.naturality (F.map f))
  have hσ := congrArg (fun g ↦ U.map g) (σ.naturality f)
  simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hη hσ
  change U₀.map (F.map f) ≫ U₀.map (η.app (F.obj V)) ≫ U.map (σ.app V) =
    (U₀.map (η.app (F.obj W)) ≫ U.map (σ.app W)) ≫
      U.map ((sheafify T.smallEtaleTopology (F ⋙ ModuleCat.extendScalars r)).map f)
  erw [← Category.assoc, hη, Category.assoc, Category.assoc, ← hσ]
  rw [ModuleCat.forget₂_map_restrictScalars]

/-- Scalar extension of roots of unity, as an abelian sheaf map.
Source: Stacks, Tag 03PK (blueprint: def-asd-ordinary-finite-p1-kummer-class). -/
def ordinaryFiniteRootMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) :
    T.rootsOfUnitySheaf N ⟶
      (RawModuleScalarComparison.forget A T).obj
        (Scheme.finiteEtaleTateLine T N A hA) :=
  ⟨{ app := fun W ↦ AddCommGrpCat.ofHom (ordinaryFiniteRootGenerator A N hA T W)
     naturality := fun _ _ f ↦ ordinaryFiniteRootGenerator_naturality A N hA T f }⟩

/-- The twist line placed in degree zero, using the existing finite etale twist.
Source: blueprint thm-amb-p1-decomposition
(blueprint: def-asd-ordinary-finite-p1-kummer-class). -/
abbrev ordinaryFiniteLine (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) : DerivedCategoryModule A T :=
  (DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateLine T N A hA)

/-- The untwisted coefficient sheaf in degree zero.
Source: blueprint thm-amb-p1-decomposition
(blueprint: def-asd-ordinary-finite-p1-kummer-class). -/
abbrev ordinaryFiniteUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategoryModule A T :=
  (DerivedCategory.singleFunctor _ 0).obj (ordinaryFiniteConstant A T)

/-- The actual scalar-extended Kummer Chern class in abelian cohomology.
The Picard class is that of the existing `ProjectiveSpace.twist ... 1`, whose
transition is `g₀ = (x₁/x₀)⁻¹ g₁`.
Source: Stacks, Tag 03PL; blueprint thm-amb-p1-decomposition
(blueprint: def-asd-ordinary-finite-p1-kummer-class). -/
@[irreducible]
def ordinaryFiniteP1KummerClass (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤))) :
    Sheaf.H ((RawModuleScalarComparison.forget A (ProjectiveLine S)).obj
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA)) 2 :=
  Sheaf.H.map (ordinaryFiniteRootMap A N hA (ProjectiveLine S)) 2
    ((ProjectiveLine S).kummerδ₁ N hP
      (Scheme.Pic.toCohomologicalPicardGroup (ProjectiveLine S)
        (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1))))

/-- The Chern-class specification predicate used by the normalized datum.
Source: Stacks Tag 03PL (blueprint: def-asd-ordinary-finite-p1-kummer-class). -/
def ordinaryFiniteP1ChernSpec (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) : Prop :=
  ordinaryFiniteClass A (ProjectiveLine S)
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2 c =
    ordinaryFiniteP1KummerClass A N hA S hP

end AlgebraicGeometry.Etale
