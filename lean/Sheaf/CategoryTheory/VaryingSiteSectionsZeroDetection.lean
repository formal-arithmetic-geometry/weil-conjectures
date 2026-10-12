/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.CategoryTheory.ColimitSites
import Sheaf.CategoryTheory.SiteFilteredColimitSections
import Sheaf.CategoryTheory.VaryingSiteInverseImageZeroDetection

/-! # Detection of zero for sections on varying sites

Source: Stacks Project, Cohomology on Sites, Tag 09YP; Sites, Tags 09YN and 0A35.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- A section of a stage sheaf which dies in the limit dies after a stage transition.
Source: Stacks Project, Sites, Tags 0A35 and 09YN; Cohomology on Sites, Tag 09YP,
first paragraph. (blueprint: lem-weil-pbc-varying-site-sections-zero-detection).

Proof: each covering of Q is the image of a finite covering at a stage, hence
is finite (including the empty covering). Apply the existing fixed-site abelian
section comparison to S and K at the limit object. Its injectivity shows that
the image of z in the colimit of the sections of S is zero. The equality criterion
for a filtered group colimit gives an arrow a to a later inverse-image sheaf
where that section is already zero. Apply varyingSite_inverseImage_zero_detection
to this arrow and section. Its inner inverse-image argument gives the required
arrow b in Under i killing the original stage section.
-/
theorem varyingSite_sections_zero_detection
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
    (K : Cocone S)
    (hK : IsColimit K)
    (i : J)
    (X_i : F.obj i)
    (t : Under i)
    (z : (Fs t.right).obj.obj (op ((F.map t.hom).toFunctor.obj X_i)))
    (hz : ((((sheafAdjunctionContinuous (V.ι.app t.right).toFunctor
        AddCommGrpCat.{u} (P t.right).toGrothendieck Q.toGrothendieck).unit.app
          (Fs t.right)).hom.app (op ((F.map t.hom).toFunctor.obj X_i))) ≫
        (eqToHom (hSobj t.right).symm ≫ K.ι.app t.right).hom.app
          (op ((V.ι.app t.right).toFunctor.obj
            ((F.map t.hom).toFunctor.obj X_i)))).hom z = 0) :
    ∃ (t' : Under i) (b : t ⟶ t'),
      ((((sheafAdjunctionContinuous (F.map b.right).toFunctor AddCommGrpCat.{u}
          (P t.right).toGrothendieck (P t'.right).toGrothendieck).unit.app
            (Fs t.right)).hom.app (op ((F.map t.hom).toFunctor.obj X_i))) ≫
        (φ b.right).hom.app (op ((F.map b.right).toFunctor.obj
          ((F.map t.hom).toFunctor.obj X_i)))).hom z = 0  := by
  have hQfinite : Q ≤ Precoverage.finite V.pt := by
    intro Y R hR
    obtain ⟨j, U, Rj, hU, hRj, hmap⟩ := (hQ Y R).mp hR
    subst Y
    subst R
    change (Rj.map (V.ι.app j).toFunctor).uncurry.Finite
    let : Finite Rj.uncurry := hfinite j U Rj hRj
    have hr : Rj.uncurry.Finite := Set.toFinite _
    apply (hr.image (fun f ↦
      ⟨(V.ι.app j).toFunctor.obj f.1, (V.ι.app j).toFunctor.map f.2⟩)).subset
    rintro ⟨Y, f⟩ hf
    cases hf with
    | of h => exact ⟨⟨_, _⟩, h, rfl⟩
  let U := (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i)
  let E := (sheafSections Q.toGrothendieck AddCommGrpCat.{u}).obj (op U)
  let T := S ⋙ E
  let z' : T.obj t.right :=
    ((((sheafAdjunctionContinuous (V.ι.app t.right).toFunctor AddCommGrpCat.{u}
      (P t.right).toGrothendieck Q.toGrothendieck).unit.app (Fs t.right)).hom.app
        (op ((F.map t.hom).toFunctor.obj X_i))) ≫
      (eqToHom (hSobj t.right).symm).hom.app (op U)).hom z
  have hiso : IsIso (colimit.desc T (E.mapCocone K)) :=
    siteFilteredColimit_sections_isIso Q hQfinite S K hK U
  have hinj := (ConcreteCategory.isIso_iff_bijective
    (colimit.desc T (E.mapCocone K))).mp hiso
  have hrep : (colimit.ι T t.right).hom z' = 0 := by
    apply hinj.1
    rw [map_zero]
    change (colimit.ι T t.right ≫ colimit.desc T (E.mapCocone K)).hom z' = 0
    rw [colimit.ι_desc]
    exact hz
  have heq : colimit.ι T t.right z' = colimit.ι T t.right 0 := by
    simpa using hrep
  obtain ⟨j', a, a', ha⟩ := Concrete.colimit_exists_of_rep_eq T z' 0 heq
  have hzero : (T.map a).hom z' = 0 := by simpa using ha
  apply varyingSite_inverseImage_zero_detection
    J F P hfinite hcover hpullback V hobjects harrows Q hQ hVcover hVpullback
    e he eV heV Fs φ hφ S hSobj hSmap i X_i t z j' a
  exact hzero

end CategoryTheory
