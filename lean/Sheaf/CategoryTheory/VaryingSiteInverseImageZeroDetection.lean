/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.CategoryTheory.ColimitSites
import Sheaf.CategoryTheory.VaryingSiteIntermediateUnitZero

/-! # Detection of zero for sections on varying sites

Source: Stacks Project, Cohomology on Sites, Tag 09YP; Sites, Tags 09YN and 0A35.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- A section killed in a later inverse-image sheaf is killed at a finite stage.
Source: Stacks Project, Sites, Tags 0A35 and 09YN, the formal double-colimit argument.
(blueprint: lem-weil-pbc-varying-site-inverse-image-zero-detection).

Proof: put X = F(t.hom)(X_i) and w = (unit_a followed by φ a)(z), a
section of Fs j' at F(a)(X). The object identity V.w a identifies the limit
image of F(a)(X) with that of X. The equation hSmap a identifies S.map a with
the inverse image of φ a preceded by eV a. Equation heV, followed by naturality
of the inverse-image unit with respect to φ a, identifies the displayed zero
section with the canonical inverse-image unit applied to w. Apply the section
formula of 0A35 to Fs j' at F(a)(X). The section w is represented at the identity
presentation via the identity inverse-image unit. The equality criterion for
this filtered colimit supplies a stage k and an arrow d : j' ⟶ k such that
the unit along d kills w. Applying φ d still gives zero. Naturality of the stage
unit, the equation he a d and the system cocycle hφ a d identify this composite
with the unit along a ≫ d followed by φ (a ≫ d), applied to z. Set t' to the
presentation i ⟶ t.right ⟶ j' ⟶ k; the arrow t ⟶ t' has right component a ≫ d.
This gives the asserted zero equation. Endpoint transports use F.map_comp,
V.w and the displayed Arrow equalities; they are additive, hence preserve zero.
The formula applies to the supplied V and Q: transport the constructed colimit
site of 0A35 through the unique colimit-category equivalence; object and arrow
colimit witnesses and hQ identify its topology with Q. This is the inner-colimit
step of 09YN, independent of any colimit K of the system.
-/
theorem varyingSite_inverseImage_zero_detection
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
    (e : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
      (sheafPullback (F.map (a ≫ b)).toFunctor AddCommGrpCat.{u} (P j).toGrothendieck (P
        l).toGrothendieck) ≅ (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u} (P
        j).toGrothendieck (P k).toGrothendieck) ⋙ (sheafPullback (F.map b).toFunctor
        AddCommGrpCat.{u} (P k).toGrothendieck (P l).toGrothendieck))
    (he : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l)
      (G : Sheaf (P j).toGrothendieck AddCommGrpCat.{u}) (X : F.obj j),
      Arrow.mk (((sheafAdjunctionContinuous (F.map (a ≫ b)).toFunctor AddCommGrpCat.{u} (P
        j).toGrothendieck (P l).toGrothendieck).unit.app G).hom.app (op X) ≫
        ((e a b).hom.app G).hom.app (op ((F.map (a ≫ b)).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map a).toFunctor AddCommGrpCat.{u} (P
        j).toGrothendieck (P k).toGrothendieck).unit.app G).hom.app (op X) ≫
        ((sheafAdjunctionContinuous (F.map b).toFunctor AddCommGrpCat.{u} (P k).toGrothendieck (P
          l).toGrothendieck).unit.app ((sheafPullback (F.map a).toFunctor AddCommGrpCat.{u} (P
          j).toGrothendieck (P k).toGrothendieck).obj G)).hom.app (op ((F.map a).toFunctor.obj
          X))))
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
    (hφ : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
      φ (a ≫ b) = (e a b).hom.app (Fs j) ≫
        (sheafPullback (F.map b).toFunctor AddCommGrpCat.{u}
          (P k).toGrothendieck (P l).toGrothendieck).map (φ a) ≫ φ b)
    (S : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (hSobj : ∀ j : J, S.obj j =
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (Fs j))
    (hSmap : ∀ {j k : J} (a : j ⟶ k),
      Arrow.mk (S.map a) = Arrow.mk ((eV a).hom.app (Fs j) ≫
        (sheafPullback (V.ι.app k).toFunctor AddCommGrpCat.{u}
          (P k).toGrothendieck Q.toGrothendieck).map (φ a)))
    (i : J)
    (X_i : F.obj i)
    (t : Under i)
    (z : (Fs t.right).obj.obj (op ((F.map t.hom).toFunctor.obj X_i)))
    (j' : J) (a : t.right ⟶ j')
    (hz : ((((sheafAdjunctionContinuous (V.ι.app t.right).toFunctor
        AddCommGrpCat.{u} (P t.right).toGrothendieck Q.toGrothendieck).unit.app
          (Fs t.right)).hom.app (op ((F.map t.hom).toFunctor.obj X_i))) ≫
        (eqToHom (hSobj t.right).symm ≫ S.map a).hom.app
          (op ((V.ι.app t.right).toFunctor.obj
            ((F.map t.hom).toFunctor.obj X_i)))).hom z = 0) :
    ∃ (t' : Under i) (b : t ⟶ t'),
      ((((sheafAdjunctionContinuous (F.map b.right).toFunctor AddCommGrpCat.{u}
          (P t.right).toGrothendieck (P t'.right).toGrothendieck).unit.app
            (Fs t.right)).hom.app (op ((F.map t.hom).toFunctor.obj X_i))) ≫
        (φ b.right).hom.app (op ((F.map b.right).toFunctor.obj
          ((F.map t.hom).toFunctor.obj X_i)))).hom z = 0 := by
  obtain ⟨k, d, hd⟩ := varyingSite_inverseImage_intermediate_unit_zero
    J F P hfinite hcover hpullback V hobjects harrows Q hQ hVcover hVpullback
    eV heV Fs φ S hSobj hSmap t.right ((F.map t.hom).toFunctor.obj X_i) z j' a hz
  let t' : Under i := Under.mk (t.hom ≫ a ≫ d)
  let b : t ⟶ t' := Under.homMk (a ≫ d) (by simp [t'])
  refine ⟨t', b, ?_⟩
  change ((((sheafAdjunctionContinuous (F.map (a ≫ d)).toFunctor AddCommGrpCat.{u}
    (P t.right).toGrothendieck (P k).toGrothendieck).unit.app (Fs t.right)).hom.app
    (op ((F.map t.hom).toFunctor.obj X_i))) ≫
    (φ (a ≫ d)).hom.app (op ((F.map (a ≫ d)).toFunctor.obj
      ((F.map t.hom).toFunctor.obj X_i)))).hom z = 0
  let X := (F.map t.hom).toFunctor.obj X_i
  let ua : (Fs t.right).obj.obj (op X) ⟶
      ((sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
        (P t.right).toGrothendieck (P j').toGrothendieck).obj
          (Fs t.right)).obj.obj (op ((F.map a).toFunctor.obj X)) :=
    ((sheafAdjunctionContinuous (F.map a).toFunctor AddCommGrpCat.{u}
      (P t.right).toGrothendieck (P j').toGrothendieck).unit.app
        (Fs t.right)).hom.app (op X)
  let uad : (Fs t.right).obj.obj (op X) ⟶
      ((sheafPullback (F.map (a ≫ d)).toFunctor AddCommGrpCat.{u}
        (P t.right).toGrothendieck (P k).toGrothendieck).obj
          (Fs t.right)).obj.obj (op ((F.map (a ≫ d)).toFunctor.obj X)) :=
    ((sheafAdjunctionContinuous (F.map (a ≫ d)).toFunctor AddCommGrpCat.{u}
      (P t.right).toGrothendieck (P k).toGrothendieck).unit.app
        (Fs t.right)).hom.app (op X)
  change (uad ≫ (φ (a ≫ d)).hom.app
    (op ((F.map (a ≫ d)).toFunctor.obj X))).hom z = 0
  rw [hφ a d]
  have hh := he a d (Fs t.right) X
  change Arrow.mk (uad ≫ ((e a d).hom.app (Fs t.right)).hom.app
      (op ((F.map (a ≫ d)).toFunctor.obj X))) =
    Arrow.mk (ua ≫
      ((sheafAdjunctionContinuous (F.map d).toFunctor AddCommGrpCat.{u}
        (P j').toGrothendieck (P k).toGrothendieck).unit.app
          ((sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
            (P t.right).toGrothendieck (P j').toGrothendieck).obj
              (Fs t.right))).hom.app (op ((F.map a).toFunctor.obj X))) at hh
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at *
  have hX : (F.map (a ≫ d)).toFunctor.obj X =
      (F.map d).toFunctor.obj ((F.map a).toFunctor.obj X) := by
    rw [F.map_comp]
    rfl
  have hh' := arrow_comp_app_eq _ _ hh
    ((sheafPullback (F.map d).toFunctor AddCommGrpCat.{u}
      (P j').toGrothendieck (P k).toGrothendieck).map (φ a) ≫ φ d).hom
    (congrArg op hX)
  apply (arrow_zero _ _ hh' z).mpr
  have hn := congrArg (fun m ↦ m.hom.app (op ((F.map a).toFunctor.obj X)))
    ((sheafAdjunctionContinuous (F.map d).toFunctor AddCommGrpCat.{u}
      (P j').toGrothendieck (P k).toGrothendieck).unit.naturality (φ a))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hn ⊢
  let A := (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
    (P t.right).toGrothendieck (P j').toGrothendieck).obj (Fs t.right)
  let Y := (F.map a).toFunctor.obj X
  let Z := (F.map d).toFunctor.obj Y
  let L := sheafPullback (F.map d).toFunctor AddCommGrpCat.{u}
    (P j').toGrothendieck (P k).toGrothendieck
  let udA : A.obj.obj (op Y) ⟶ (L.obj A).obj.obj (op Z) :=
    ((sheafAdjunctionContinuous (F.map d).toFunctor AddCommGrpCat.{u}
      (P j').toGrothendieck (P k).toGrothendieck).unit.app A).hom.app (op Y)
  let udF : (Fs j').obj.obj (op Y) ⟶ (L.obj (Fs j')).obj.obj (op Z) :=
    ((sheafAdjunctionContinuous (F.map d).toFunctor AddCommGrpCat.{u}
      (P j').toGrothendieck (P k).toGrothendieck).unit.app (Fs j')).hom.app (op Y)
  let f := (φ a).hom.app (op Y)
  let g := (L.map (φ a)).hom.app (op Z)
  let q := (φ d).hom.app (op Z)
  change f ≫ udF = udA ≫ g at hn
  change ((ua ≫ udA) ≫ g ≫ q).hom z = 0
  rw [Category.assoc, ← Category.assoc udA g q, ← hn]
  change q.hom ((ua ≫ f ≫ udF).hom z) = 0
  have hd' : (ua ≫ f ≫ udF).hom z = 0 := hd
  rw [hd', map_zero]

end CategoryTheory
