/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.CategoryTheory.ColimitSites
import Sheaf.CategoryTheory.ColimitSiteUnitZeroDetection

/-! # Finite-stage detection for the intermediate inverse-image unit

Source: Stacks Project, Sites, Tags 0A35 and 09YN.
(blueprint: lem-weil-pbc-varying-site-intermediate-unit-zero).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Postcompose equal Arrow objects at equal evaluation objects. -/
theorem arrow_comp_app_eq {C : Type u} [SmallCategory C]
    {B D : C ⥤ AddCommGrpCat.{u}} {A : AddCommGrpCat.{u}} {X Y : C}
    (f : A ⟶ B.obj X) (g : A ⟶ B.obj Y) (h : Arrow.mk f = Arrow.mk g)
    (η : B ⟶ D) (hXY : X = Y) :
    Arrow.mk (f ≫ η.app X) = Arrow.mk (g ≫ η.app Y) := by
  subst hXY
  rw [Arrow.mk_inj] at h
  rw [h]

/-- Equal Arrow objects with a common source have the same zero kernel. -/
theorem arrow_zero {A B C : AddCommGrpCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (h : Arrow.mk f = Arrow.mk g) (x : A) : f.hom x = 0 ↔ g.hom x = 0 := by
  obtain ⟨hA, hB, hfg⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  subst hB
  simpa using congrArg (fun k : A ⟶ B ↦ k.hom x = 0) hfg

private theorem arrow_source_eq {C : Type v} [Category.{u} C]
    {A A' B B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    (h : Arrow.mk f = Arrow.mk g) (hA : A = A') :
    Arrow.mk (eqToHom hA.symm ≫ f) = Arrow.mk g := by
  subst hA
  obtain ⟨hA, hB, hfg⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  subst hB
  simpa using h

private theorem arrow_precomp_eq {C : Type v} [Category.{u} C]
    {A B B' D : C} (f : A ⟶ B) (g : A ⟶ B')
    (h : Arrow.mk f = Arrow.mk g) (v : D ⟶ A) :
    Arrow.mk (v ≫ f) = Arrow.mk (v ≫ g) := by
  obtain ⟨hA, hB, hfg⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  subst hB
  have hfg' : f = g := by simpa using hfg
  rw [hfg']

/-- The image after one coefficient transition is killed by a later inverse-image unit.
Source: Stacks Project, Sites, Tag 0A35, equation-compute-pullback-to-limit;
Tag 09YN, the inner colimit in the double-colimit argument.
(blueprint: lem-weil-pbc-varying-site-intermediate-unit-zero).

Proof: Set w equal to the unit along a followed by the coefficient map phi a,
applied to z. Cocone naturality identifies V_j(X) with V_j'(F_a(X)). Use hSmap
and hSobj to replace the displayed system map by eV_a followed by the inverse
image of phi a. The unit equation heV and naturality of the adjunction unit in
phi a identify its value with the limit-site unit of w, up to additive endpoint
transports. Thus that limit-site unit kills w. The object and arrow colimit
witnesses identify V with the constructed filtered colimit category by its
unique colimit equivalence. The image-covering characterization hQ transports
its topology to Q. Transport the inverse-image section formula of Tag 0A35
through this equivalence; uniqueness of left adjoints identifies its unit with
the specified unit. In that formula w is represented at the identity stage.
The filtered-colimit equality criterion applied to w and zero supplies a later
arrow d where the unit image of w is zero. Identity inverse-image units are
isomorphisms, so the identity representative gives the asserted equation.
All transports are additive and preserve zero. No coefficient map phi d or
finite-stage composition cocycle is used in this argument.
-/
theorem varyingSite_inverseImage_intermediate_unit_zero
    (J : Type u)
    [SmallCategory J]
    [IsFiltered J]
    (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos]
    [∀ j, (P j).IsStableUnderComposition]
    [∀ j, (P j).IsStableUnderBaseChange]
    [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteColimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos]
    [Q.IsStableUnderComposition]
    [Q.IsStableUnderBaseChange]
    [Q.HasPullbacks]
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X)
        (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    (hVcover : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      R.map (V.ι.app j).toFunctor ∈ Q ((V.ι.app j).toFunctor.obj X))
    (hVpullback : ∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (V.ι.app j).toFunctor)
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    [∀ j : J, PreservesFiniteLimits (sheafPullback (V.ι.app j).toFunctor (Type u)
      (P j).toGrothendieck Q.toGrothendieck)]
    [∀ j : J, PreservesFiniteColimits (sheafPullback (V.ι.app j).toFunctor (Type u)
      (P j).toGrothendieck Q.toGrothendieck)]
    (eV : ∀ {j k : J} (a : j ⟶ k),
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u} (P j).toGrothendieck
        Q.toGrothendieck) ≅ (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u} (P
        j).toGrothendieck (P k).toGrothendieck) ⋙ (sheafPullback (V.ι.app k).toFunctor
        AddCommGrpCat.{u} (P k).toGrothendieck Q.toGrothendieck))
    (heV : ∀ {j k : J} (a : j ⟶ k)
      (G : Sheaf (P j).toGrothendieck AddCommGrpCat.{u}) (X : F.obj j),
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u} (P
        j).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X) ≫
        ((eV a).hom.app G).hom.app (op ((V.ι.app j).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map a).toFunctor AddCommGrpCat.{u} (P
        j).toGrothendieck (P k).toGrothendieck).unit.app G).hom.app (op X) ≫
        ((sheafAdjunctionContinuous (V.ι.app k).toFunctor AddCommGrpCat.{u} (P k).toGrothendieck
          Q.toGrothendieck).unit.app ((sheafPullback (F.map a).toFunctor AddCommGrpCat.{u} (P
          j).toGrothendieck (P k).toGrothendieck).obj G)).hom.app (op ((F.map a).toFunctor.obj
          X))))
    (Fs : ∀ j : J, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (φ : ∀ {j k : J} (a : j ⟶ k),
      (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck (P k).toGrothendieck).obj (Fs j) ⟶ Fs k)
    (S : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (hSobj : ∀ j : J, S.obj j =
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (Fs j))
    (hSmap : ∀ {j k : J} (a : j ⟶ k),
      Arrow.mk (S.map a) = Arrow.mk ((eV a).hom.app (Fs j) ≫
        (sheafPullback (V.ι.app k).toFunctor AddCommGrpCat.{u}
          (P k).toGrothendieck Q.toGrothendieck).map (φ a)))
    (j : J) (X : F.obj j) (z : (Fs j).obj.obj (op X))
    (j' : J) (a : j ⟶ j')
    (hz : ((((sheafAdjunctionContinuous (V.ι.app j).toFunctor
        AddCommGrpCat.{u} (P j).toGrothendieck Q.toGrothendieck).unit.app
          (Fs j)).hom.app (op X)) ≫
        (eqToHom (hSobj j).symm ≫ S.map a).hom.app
          (op ((V.ι.app j).toFunctor.obj X))).hom z = 0) :
    ∃ (k : J) (d : j' ⟶ k),
      ((((sheafAdjunctionContinuous (F.map a).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck (P j').toGrothendieck).unit.app
            (Fs j)).hom.app (op X)) ≫
        (φ a).hom.app (op ((F.map a).toFunctor.obj X)) ≫
        ((sheafAdjunctionContinuous (F.map d).toFunctor AddCommGrpCat.{u}
          (P j').toGrothendieck (P k).toGrothendieck).unit.app
            (Fs j')).hom.app (op ((F.map a).toFunctor.obj X))).hom z = 0 := by
  let U := (V.ι.app j).toFunctor.obj X
  let Y := (F.map a).toFunctor.obj X
  let L := sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
    (P j).toGrothendieck (P j').toGrothendieck
  let T := sheafPullback (V.ι.app j').toFunctor AddCommGrpCat.{u}
    (P j').toGrothendieck Q.toGrothendieck
  let uv : (Fs j).obj.obj (op X) ⟶
      ((sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (Fs j)).obj.obj (op U) :=
    ((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
      (P j).toGrothendieck Q.toGrothendieck).unit.app (Fs j)).hom.app (op X)
  let ua : (Fs j).obj.obj (op X) ⟶ (L.obj (Fs j)).obj.obj (op Y) :=
    ((sheafAdjunctionContinuous (F.map a).toFunctor AddCommGrpCat.{u}
      (P j).toGrothendieck (P j').toGrothendieck).unit.app (Fs j)).hom.app (op X)
  have hs := arrow_source_eq _ _ (hSmap a) (hSobj j)
  have hse := congrArg
    (fun r : Arrow (Sheaf Q.toGrothendieck AddCommGrpCat.{u}) ↦
      Arrow.mk (r.hom.hom.app (op U))) hs
  have hsu := arrow_precomp_eq _ _ hse uv
  have hz' := (arrow_zero _ _ hsu z).mp hz
  change (uv ≫ ((eV a).hom.app (Fs j) ≫ T.map (φ a)).hom.app (op U)).hom z = 0
    at hz'
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hz'
  have hh := heV a (Fs j) X
  have hU : U = (V.ι.app j').toFunctor.obj Y := by
    have h := congrArg (fun f ↦ f.toFunctor.obj X) (V.w a)
    exact h.symm
  have hh' := arrow_comp_app_eq _ _ hh (T.map (φ a)).hom (congrArg op hU)
  have hz'' :
      ((ua ≫
        ((sheafAdjunctionContinuous (V.ι.app j').toFunctor AddCommGrpCat.{u}
          (P j').toGrothendieck Q.toGrothendieck).unit.app
            (L.obj (Fs j))).hom.app (op Y)) ≫
        (T.map (φ a)).hom.app (op ((V.ι.app j').toFunctor.obj Y))).hom z = 0 := by
    apply (arrow_zero _ _ hh' z).mp
    change ((uv ≫ ((eV a).hom.app (Fs j)).hom.app (op U)) ≫
      (T.map (φ a)).hom.app (op U)).hom z = 0
    rw [Category.assoc]
    exact hz'
  have hn := congrArg (fun m ↦ m.hom.app (op Y))
    ((sheafAdjunctionContinuous (V.ι.app j').toFunctor AddCommGrpCat.{u}
      (P j').toGrothendieck Q.toGrothendieck).unit.naturality (φ a))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hn
  let uvL : (L.obj (Fs j)).obj.obj (op Y) ⟶
      (T.obj (L.obj (Fs j))).obj.obj (op ((V.ι.app j').toFunctor.obj Y)) :=
    ((sheafAdjunctionContinuous (V.ι.app j').toFunctor AddCommGrpCat.{u}
      (P j').toGrothendieck Q.toGrothendieck).unit.app
        (L.obj (Fs j))).hom.app (op Y)
  let uvF : (Fs j').obj.obj (op Y) ⟶
      (T.obj (Fs j')).obj.obj (op ((V.ι.app j').toFunctor.obj Y)) :=
    ((sheafAdjunctionContinuous (V.ι.app j').toFunctor AddCommGrpCat.{u}
      (P j').toGrothendieck Q.toGrothendieck).unit.app (Fs j')).hom.app (op Y)
  let f := (φ a).hom.app (op Y)
  let g := (T.map (φ a)).hom.app (op ((V.ι.app j').toFunctor.obj Y))
  change f ≫ uvF = uvL ≫ g at hn
  change ((ua ≫ uvL) ≫ g).hom z = 0 at hz''
  rw [Category.assoc, ← hn] at hz''
  obtain ⟨k, d, hd⟩ := colimitSite_unit_zero_detection
    J F P hfinite hcover hpullback V hobjects harrows Q hQ hVcover hVpullback
    j' (Fs j') Y ((ua ≫ f).hom z) hz''
  exact ⟨k, d, hd⟩

end CategoryTheory
