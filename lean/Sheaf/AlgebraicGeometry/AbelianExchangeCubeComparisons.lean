/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical comparison maps for a base-change cube

Source: Stacks Project, Tags 03Q9 and 095T, restriction of section complexes.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons).
-/

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme

/-- Apply homology and the inverse-image stalk comparison to a derived morphism.
The equality specifies the point at which its source stalk is taken.
Source: Stacks Project, Tag 03Q1.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons). -/
noncomputable def derivedStalkComparison
    {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ Z) (s : Spec (.of k) ⟶ Y) (h : t ≫ a = s)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (m : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ L) (q : ℤ) :
    (pointSmallEtale s).sheafFiber.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ⟶
      (pointSmallEtale t).sheafFiber.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj L) := by
  subst s
  exact (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} a t).inv.app _ ≫
    (pointSmallEtale t).sheafFiber.map
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        ((a)^*[AddCommGrpCat.{u + 1}]) q).hom.app K ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map m)

variable {S T X X' S₀ T₀ X₀ X₁ : Scheme.{u}}
  {g : T ⟶ S} {f : X ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ T}
  {jA : S₀ ⟶ S} {jB : T₀ ⟶ T} {g₀ : T₀ ⟶ S₀}
  {p₀ : X₀ ⟶ X} {f₀ : X₀ ⟶ S₀} {p₁ : X₁ ⟶ X₀} {f₁ : X₁ ⟶ T₀}
  {b : X₁ ⟶ X'}

/-- Restrict the source of exchange: commute the two inverse images, use the
base-change map for f, and identify the pulled-back single complex.
Source: Stacks Project, Tag 03Q9, restriction complexes.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons). -/
noncomputable def exchangeCubeSourceComparison
    (sq₀ : CommSq p₀ f₀ f jA) (h : jB ≫ g = g₀ ≫ jA)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    (D+((jB)^*[AddCommGrpCat.{u + 1}])).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙ D+((g)^*[AddCommGrpCat.{u + 1}])).obj K) ⟶
    (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙ D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀ :=
  (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} jB g).inv.app _ ≫
    eqToHom (congrArg (fun a ↦ (D+((a)^*[AddCommGrpCat.{u + 1}])).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) h) ≫
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g₀ jA).hom.app _ ≫
    (D+((g₀)^*[AddCommGrpCat.{u + 1}])).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀).app _ ≫
        (R+((f₀)_*[AddCommGrpCat.{u + 1}])).map
          ((Functor.mapDerivedCategoryPlusSingleFunctor
            ((p₀)^*[AddCommGrpCat.{u + 1}]) 0).hom.app G))

/-- Restrict the target of exchange: use the base-change map for f', then commute
inverse images and identify the pulled-back single complex.
Source: Stacks Project, Tag 03Q9, restriction complexes.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons). -/
noncomputable def exchangeCubeTargetComparison
    (sqB : CommSq b f₁ f' jB) (hb : b ≫ g' = p₁ ≫ p₀)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    (D+((jB)^*[AddCommGrpCat.{u + 1}])).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙ R+((f')_*[AddCommGrpCat.{u + 1}])).obj K) ⟶
    (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙ R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀ :=
  (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqB).app _ ≫
    (R+((f₁)_*[AddCommGrpCat.{u + 1}])).map
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b g').inv.app _ ≫
        eqToHom (congrArg (fun a ↦ (D+((a)^*[AddCommGrpCat.{u + 1}])).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) hb) ≫
        (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} p₁ p₀).hom.app _ ≫
        (D+((p₁)^*[AddCommGrpCat.{u + 1}])).map
          ((Functor.mapDerivedCategoryPlusSingleFunctor
            ((p₀)^*[AddCommGrpCat.{u + 1}]) 0).hom.app G))

/-- The exchange square commutes after restriction along a commuting cube and on
homology stalks. This is a compatibility assertion only, with no invertibility claim.
Source: Stacks Project, Tags 03Q9 and 095T; formal mate-pasting calculation.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons).

Proof: paste the original square with the square over jB, and paste the square over
jA with the local square over g₀. The resulting outer squares have equal horizontal
maps by h and hb. The horizontal pasting law for the derived base-change map gives
the same outer mate from each factorization. Cancel the inverse-image composition
isomorphisms to get the square between the two comparison morphisms above. Naturality
of the inverse-image/single-complex isomorphism inserts the identification of K₀.
Apply H^q, then the point fibre functor. Naturality of the exact inverse-image/homology
isomorphism and of the inverse-image stalk isomorphism identifies the source with the
stalk at s and gives the displayed square. No cartesianness, properness, torsion, or
strict locality is required; the argument also applies to q = 0 and zero sheaves. -/
theorem exchangeCube_stalk_square
    (sq : CommSq g' f' f g) (sq₀ : CommSq p₀ f₀ f jA)
    (sq₁ : CommSq p₁ f₁ f₀ g₀) (sqB : CommSq b f₁ f' jB)
    (h : jB ≫ g = g₀ ≫ jA) (hb : b ≫ g' = p₁ ≫ p₀)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ T₀) (s : Spec (.of k) ⟶ T) (ht : t ≫ jB = s)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    let M₁ := (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g)^*[AddCommGrpCat.{u + 1}])).obj K
    let M₂ := (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f')_*[AddCommGrpCat.{u + 1}])).obj K
    let N₁ := (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀
    let N₂ := (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀
    let H := DerivedCategory.Plus.homologyFunctor _ q
    derivedStalkComparison jB t s ht M₁ N₁ (exchangeCubeSourceComparison sq₀ h G) q ≫
        (pointSmallEtale t).sheafFiber.map
          (H.map ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁).app K₀)) =
      (pointSmallEtale s).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map
            ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K)) ≫
        derivedStalkComparison jB t s ht M₂ N₂
          (exchangeCubeTargetComparison sqB hb G) q := by sorry

end AlgebraicGeometry.Etale
