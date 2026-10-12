/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.CategoryTheory.ColimitSites
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.ColimitSiteCechComplex
import Sheaf.CategoryTheory.SiteCechVanishingCriterion
import Sheaf.CategoryTheory.SiteInjectiveCechAcyclic
import Sheaf.Paper.ColimitSitesInjectiveSystem

/-! # Acyclic coefficient replacements on colimit sites.

Source: Stacks Project, Tags 09YP, 0739 and 09YN.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- A compatible coefficient replacement has an acyclic middle colimit and natural boundaries.
Source: Stacks Project, Tags 0EXZ and 09YP (the injective embedding and Cech vanishing),
and Tag 0739 (the cokernel short exact sequence and its natural connecting maps).
(blueprint: lem-weil-pbc-colimit-sites-acyclic-replacement).

Proof:
Identify identity inverse image with the identity functor using the adjunction unit.
The cocycle makes the identity coefficient actions idempotent. Split their images in
abelian sheaves and restrict every transition; coherence of the units identifies the
resulting inverse-image diagram with S, since S.map_id and hSmap make the pulled-back
idempotents identities. Transpose the normalized transitions through the adjunctions,
apply exists_compatible_injective_system (0EXZ), and transpose its embedding back.
Take stage cokernels FsR. Exact inverse image transports the short exact sequences;
cancelling their cokernel epimorphisms proves hφR and the laws defining SR. Choose KR.
Exact filtered colimits give the short exact sequence K.pt → G → KR.pt.
Every covering descends by hQ to a finite stage covering. The colimit-site Cech
comparison identifies G's Cech complex with the filtered colimit of the injective
stage complexes. Injective Cech acyclicity and exact filtered colimits imply positive
Cech vanishing; the site Cech vanishing criterion gives the asserted H' vanishing.
Take d to be Yoneda postcomposition with the target short exact sequence class;
this gives its pointwise formula. At each stage take the boundary of the normalized
short exact sequence, then compose
with the normalized inclusion on cohomology to obtain β. Naturality of the long exact
sequence and the connecting clauses of hcanonicalMap give the displayed square with
the target Yoneda-product boundary. The hU transports identify the two site objects.
No cohomology diagram, comparison cocone, or surjectivity assertion is constructed here.
-/
theorem colimit_sites_acyclic_replacement
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
    (i : J) (X_i : F.obj i) (n : ℕ)
    (hU : ∀ t : Under i,
      (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i) =
        (V.ι.app i).toFunctor.obj X_i) :
    ∃(FsR : ∀ j : J, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (φR : ∀ {j k : J} (a : j ⟶ k),
      (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck (P k).toGrothendieck).obj (FsR j) ⟶ FsR k)
    (hφR : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
      φR (a ≫ b) = (e a b).hom.app (FsR j) ≫
        (sheafPullback (F.map b).toFunctor AddCommGrpCat.{u}
          (P k).toGrothendieck (P l).toGrothendieck).map (φR a) ≫ φR b)
    (SR : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (hSobjR : ∀ j : J, SR.obj j =
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (FsR j))
    (hSmapR : ∀ {j k : J} (a : j ⟶ k),
      Arrow.mk (SR.map a) = Arrow.mk ((eV a).hom.app (FsR j) ≫
        (sheafPullback (V.ι.app k).toFunctor AddCommGrpCat.{u}
          (P k).toGrothendieck Q.toGrothendieck).map (φR a)))
    (KR : Cocone SR) (hKR : IsColimit KR)
    (hidR : ∀ (j : J) (X : F.obj j),
      Arrow.mk (pullbackMap (𝟙 j) n X (FsR j) ≫
        ((Sheaf.cohomologyPresheafFunctor (P j).toGrothendieck n).map
          (φR (𝟙 j))).app (op ((F.map (𝟙 j)).toFunctor.obj X))) =
        Arrow.mk (𝟙 (Sheaf.H' (FsR j) n X)))
    (G : Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (f : K.pt ⟶ G) (g : G ⟶ KR.pt) (w : f ≫ g = 0)
    (hE : (ShortComplex.mk f g w).ShortExact)
    (d : Sheaf.H' KR.pt n ((V.ι.app i).toFunctor.obj X_i) ⟶
      Sheaf.H' K.pt (n + 1) ((V.ι.app i).toFunctor.obj X_i)),
      (∀ x, d.hom x = Abelian.Ext.comp x hE.extClass rfl) ∧
      (∀ (U : V.pt) (q : ℕ), 0 < q → IsZero (Sheaf.H' G q U)) ∧
      ∃ β : ∀ t : Under i,
        Sheaf.H' (FsR t.right) n ((F.map t.hom).toFunctor.obj X_i) ⟶
          Sheaf.H' (Fs t.right) (n + 1) ((F.map t.hom).toFunctor.obj X_i),
        ∀ t : Under i,
          β t ≫ (canonicalMap t.right (n + 1)
          ((F.map t.hom).toFunctor.obj X_i) (Fs t.right) ≫
        ((Sheaf.cohomologyPresheafFunctor Q.toGrothendieck (n + 1)).map
          (eqToHom (hSobj t.right).symm ≫ K.ι.app t.right)).app
            (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i)))) ≫
              eqToHom (congrArg (Sheaf.H' K.pt (n + 1)) (hU t)) =
            (canonicalMap t.right n
          ((F.map t.hom).toFunctor.obj X_i) (FsR t.right) ≫
        ((Sheaf.cohomologyPresheafFunctor Q.toGrothendieck n).map
          (eqToHom (hSobjR t.right).symm ≫ KR.ι.app t.right)).app
            (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i)))) ≫
              eqToHom (congrArg (Sheaf.H' KR.pt n) (hU t)) ≫
              d
    := by sorry

end CategoryTheory
