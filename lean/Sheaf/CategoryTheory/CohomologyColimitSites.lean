/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.CategoryTheory.ColimitSites
public import Sheaf.CategoryTheory.SiteCohomologyPullback
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Sheaf.CategoryTheory.CohomologyColimitSitesClassDescent
import Sheaf.CategoryTheory.CohomologyColimitSitesEventualVanishing

/-! # Cohomology on a colimit of sites

Source: Stacks Project, Cohomology on Sites, Lemma 09YP, in Situation 0A34.
(blueprint: lem-weil-pbc-cohomology-colimit-of-sites).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Source: Stacks Project, Cohomology on Sites, Lemma 09YP, with Lemmas 0EXZ and 0739.
(blueprint: lem-weil-pbc-cohomology-colimit-of-sites).

Proof: split continuity into finite-stage existence and finite-stage detection of zero.
The two lemmas below retain the source's degree-zero and dimension-shifting argument.
Every element of the filtered group colimit has a stage representative. If its image
is zero, eventual vanishing supplies a later transition killing that representative;
the colimit transition equation then makes the original element zero. Thus the
comparison has trivial kernel and is injective. Finite-stage existence gives a lift
of every target element along a coprojection, so the comparison is surjective.
The forgetful functor on abelian groups reflects isomorphisms, yielding the conclusion.

The equalities in Arrow include endpoint transports. F.map_comp and the relation
`t.hom ≫ b.right = t'.hom` in Under i identify the endpoints in hDmap;
V.w t.hom identifies them in hclegs. The unit equations he and heV fix the composition
isomorphisms; hpullbackMap and hcanonicalMap characterize the cohomology pullbacks.
-/
theorem cohomology_colimit_of_sites
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderComposition]
    [∀ j, (P j).IsStableUnderBaseChange] [∀ j, (P j).HasPullbacks]
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
    [Q.HasIsos] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange] [Q.HasPullbacks]
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
    [∀ (j k : J) (a : j ⟶ k),
      (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck (P k).toGrothendieck).Additive]
    [∀ j : J, (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
      (P j).toGrothendieck Q.toGrothendieck).Additive]
    [∀ j : J, HasExt.{u} (Sheaf (P j).toGrothendieck AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf Q.toGrothendieck AddCommGrpCat.{u})]
    (pullbackMap : ∀ {j k : J} (a : j ⟶ k) (q : ℕ) (X : F.obj j)
      (A : Sheaf (P j).toGrothendieck AddCommGrpCat.{u}),
      Sheaf.H' A q X ⟶ Sheaf.H' ((sheafPullback (F.map a).toFunctor AddCommGrpCat.{u} (P
        j).toGrothendieck (P k).toGrothendieck).obj A) q ((F.map a).toFunctor.obj X))
    (hpullbackMap : ∀ {j k : J} (a : j ⟶ k),
      (∀ (p : ℕ) (X : F.obj j) (A A' : Sheaf (P j).toGrothendieck AddCommGrpCat.{u}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor (P j).toGrothendieck p).map φ).app (op X) ≫
            pullbackMap a p X A' =
          pullbackMap a p X A ≫
            ((Sheaf.cohomologyPresheafFunctor (P k).toGrothendieck p).map
              ((sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
                (P j).toGrothendieck (P k).toGrothendieck).map φ)).app (op ((F.map
                  a).toFunctor.obj X))) ∧
      (∀ (S : ShortComplex (Sheaf (P j).toGrothendieck AddCommGrpCat.{u})) (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck (P k).toGrothendieck)).ShortExact)
        (p : ℕ) (X : F.obj j) (x : Sheaf.H' S.X₃ p X),
        (pullbackMap a (p + 1) X S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((pullbackMap a p X S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (X : F.obj j) (A : Sheaf (P j).toGrothendieck AddCommGrpCat.{u}) (x : Sheaf.H' A 0 X),
        ((Abelian.Ext.addEquiv₀ ((pullbackMap a 0 X A).hom x)).hom.app (op ((F.map
          a).toFunctor.obj X))).hom
            (((toSheafify (P k).toGrothendieck
              (yoneda.obj ((F.map a).toFunctor.obj X) ⋙ AddCommGrpCat.free)).app (op ((F.map
                a).toFunctor.obj X))).hom
                (FreeAbelianGroup.of (𝟙 ((F.map a).toFunctor.obj X)))) =
          (((sheafAdjunctionContinuous (F.map a).toFunctor AddCommGrpCat.{u}
            (P j).toGrothendieck (P k).toGrothendieck).unit.app A).hom.app (op X)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op X)).hom
              (((toSheafify (P j).toGrothendieck
                (yoneda.obj X ⋙ AddCommGrpCat.free)).app (op X)).hom
                  (FreeAbelianGroup.of (𝟙 X))))))
    (canonicalMap : ∀ (j : J) (q : ℕ) (X : F.obj j)
      (A : Sheaf (P j).toGrothendieck AddCommGrpCat.{u}),
      Sheaf.H' A q X ⟶ Sheaf.H' ((sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u} (P
        j).toGrothendieck Q.toGrothendieck).obj A) q ((V.ι.app j).toFunctor.obj X))
    (hcanonicalMap : ∀ (j : J),
      (∀ (p : ℕ) (X : F.obj j) (A A' : Sheaf (P j).toGrothendieck AddCommGrpCat.{u}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor (P j).toGrothendieck p).map φ).app (op X) ≫
            canonicalMap j p X A' =
          canonicalMap j p X A ≫
            ((Sheaf.cohomologyPresheafFunctor Q.toGrothendieck p).map
              ((sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
                (P j).toGrothendieck Q.toGrothendieck).map φ)).app (op ((V.ι.app j).toFunctor.obj
                  X))) ∧
      (∀ (S : ShortComplex (Sheaf (P j).toGrothendieck AddCommGrpCat.{u})) (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck Q.toGrothendieck)).ShortExact)
        (p : ℕ) (X : F.obj j) (x : Sheaf.H' S.X₃ p X),
        (canonicalMap j (p + 1) X S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((canonicalMap j p X S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (X : F.obj j) (A : Sheaf (P j).toGrothendieck AddCommGrpCat.{u}) (x : Sheaf.H' A 0 X),
        ((Abelian.Ext.addEquiv₀ ((canonicalMap j 0 X A).hom x)).hom.app (op ((V.ι.app
          j).toFunctor.obj X))).hom
            (((toSheafify Q.toGrothendieck
              (yoneda.obj ((V.ι.app j).toFunctor.obj X) ⋙ AddCommGrpCat.free)).app (op ((V.ι.app
                j).toFunctor.obj X))).hom
                (FreeAbelianGroup.of (𝟙 ((V.ι.app j).toFunctor.obj X)))) =
          (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
            (P j).toGrothendieck Q.toGrothendieck).unit.app A).hom.app (op X)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op X)).hom
              (((toSheafify (P j).toGrothendieck
                (yoneda.obj X ⋙ AddCommGrpCat.free)).app (op X)).hom
                  (FreeAbelianGroup.of (𝟙 X))))))
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
    (K : Cocone S) (hK : IsColimit K)
    (i : J) (X_i : F.obj i) (p : ℕ)
    (D : Under i ⥤ AddCommGrpCat.{u})
    (hDobj : ∀ t : Under i,
      D.obj t = Sheaf.H' (Fs t.right) p ((F.map t.hom).toFunctor.obj X_i))
    (hDmap : ∀ {t t' : Under i} (b : t ⟶ t'),
      Arrow.mk (D.map b) = Arrow.mk
        (pullbackMap b.right p ((F.map t.hom).toFunctor.obj X_i) (Fs t.right) ≫
          ((Sheaf.cohomologyPresheafFunctor (P t'.right).toGrothendieck p).map
            (φ b.right)).app
              (op ((F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i)))))
    (c : Cocone D)
    (hcpt : c.pt = Sheaf.H' K.pt p ((V.ι.app i).toFunctor.obj X_i))
    (hclegs : ∀ t : Under i, Arrow.mk (c.ι.app t) = Arrow.mk
      (canonicalMap t.right p ((F.map t.hom).toFunctor.obj X_i) (Fs t.right) ≫
        ((Sheaf.cohomologyPresheafFunctor Q.toGrothendieck p).map
          (eqToHom (hSobj t.right).symm ≫ K.ι.app t.right)).app
            (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i))))) :
    IsIso (colimit.desc D c) := by
  have hlift := cohomology_colimit_sites_class_descent
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVcover hVpullback
      pullbackMap hpullbackMap canonicalMap hcanonicalMap e he eV heV Fs φ hφ
      S hSobj hSmap K hK i X_i p D hDobj hDmap c hcpt hclegs
  have hzero := cohomology_colimit_sites_eventual_vanishing
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVcover hVpullback
      pullbackMap hpullbackMap canonicalMap hcanonicalMap e he eV heV Fs φ hφ
      S hSobj hSmap K hK i X_i p D hDobj hDmap c hcpt hclegs
  apply (ConcreteCategory.isIso_iff_bijective (colimit.desc D c)).2
  constructor
  · apply (injective_iff_map_eq_zero (colimit.desc D c).hom).2
    intro z hz
    obtain ⟨t, x, rfl⟩ := Concrete.colimit_exists_rep D z
    have hx : (c.ι.app t).hom x = 0 := by
      change (colimit.ι D t ≫ colimit.desc D c).hom x = 0 at hz
      rwa [colimit.ι_desc] at hz
    obtain ⟨t', b, hb⟩ := hzero t x hx
    calc
      (colimit.ι D t).hom x = (colimit.ι D t').hom ((D.map b).hom x) :=
        (colimit.w_apply D b x).symm
      _ = 0 := by rw [hb, map_zero]
  · intro y
    obtain ⟨t, x, hx⟩ := hlift y
    refine ⟨(colimit.ι D t).hom x, ?_⟩
    change (colimit.ι D t ≫ colimit.desc D c).hom x = y
    rw [colimit.ι_desc]
    exact hx

end CategoryTheory
