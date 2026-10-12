/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.CategoryTheory.ColimitSites
public import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.CohomologyColimitSitesShortExactSystems
import Sheaf.CategoryTheory.CohomologyColimitSitesBoundaryDiagrams
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Exact ladders before finite-stage correction

Source: Stacks Project, Cohomology on Sites, Tags 09YP and 0EXZ; Sites, Tag 09YN.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

set_option maxHeartbeats 1000000 in
-- The dependent continuation elaborates many sheaf-pullback and Ext endpoints.
set_option linter.unusedVariables false in
-- Proof binders in the original continuation are required witnesses, even when unused in result.
/-- The exact cohomology ladder for a compatible injective embedding, before any
finite-stage correction is chosen. The two returned coefficient systems are its cokernel
and its injective middle term. Only stage surjectivity and target exactness are asserted;
there is no finite-stage descent or corrected-lift assertion in this statement.
The witnesses are supplied in continuation form to avoid repeated dependent
existential elimination of the large site expressions.

Source: Stacks Project, Tags 09YP and 0739 (the two-row exact diagram), using 0EXZ.
(blueprint: lem-weil-pbc-colimit-sites-exact-ladder).

Proof: normalize the identity actions of Fs by splitting their idempotents in the
abelian sheaf categories. The functor identity laws for S and D imply that these
splittings induce isomorphisms on the specified inverse-image diagram and degree-(n+1)
stage groups. Exact inverse image preserves these splittings. Transpose the normalized
transitions through the inverse-image/pushforward adjunctions; the unit coherences he
and heV identify the resulting cocycles. Apply the compatible injective-system
embedding of Tag 0EXZ and transpose back. Let Gs be its injective middle terms and Rs
the cokernels. Exact inverse images give compatible cokernel transitions; cancel the
cokernel epimorphisms to verify their cocycle. Form the inverse-image diagrams U and T
and their colimit cocones M and L. Exact filtered colimits and exact inverse image
give a short exact sequence with first term K.pt, middle term M.pt and last term L.pt.
Form B and E from degree-n cohomology of Gs and Rs, and their canonical cocones b and d.
Naturality in coefficients and compatibility with connecting maps give the maps
alpha and delta and their naturality; endpoint equations are transported exactly as
in hDobj and hDmap. The supplied pullback maps agree with the actual site pullback
maps: naturality and connecting compatibility determine positive degrees by injective
dimension shifting from the specified degree-zero unit formula. The stage long exact
sequences give alpha followed by delta equal to zero, and delta is surjective because
Gs is injective and n+1 is positive. The target long exact sequence gives alpha0 and
beta and exactness at d.pt: any class killed by beta comes from b.pt. The canonical-map
connecting compatibility and naturality give both squares. No target injective
acyclicity or finite-stage descent is used here.
-/
theorem cohomology_colimit_sites_exact_ladder (n : ℕ)
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
    (K : Cocone S)
    (hK : IsColimit K)
    (i : J)
    (X_i : F.obj i)
    (D : Under i ⥤ AddCommGrpCat.{u})
    (hDobj : ∀ t : Under i,
      D.obj t = Sheaf.H' (Fs t.right) (n + 1) ((F.map t.hom).toFunctor.obj X_i))
    (hDmap : ∀ {t t' : Under i} (b : t ⟶ t'),
      Arrow.mk (D.map b) = Arrow.mk
        (pullbackMap b.right (n + 1) ((F.map t.hom).toFunctor.obj X_i) (Fs t.right) ≫
          ((Sheaf.cohomologyPresheafFunctor (P t'.right).toGrothendieck (n + 1)).map
            (φ b.right)).app
              (op ((F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i)))))
    (c : Cocone D)
    (hcpt : c.pt = Sheaf.H' K.pt (n + 1) ((V.ι.app i).toFunctor.obj X_i))
    (hclegs : ∀ t : Under i, Arrow.mk (c.ι.app t) = Arrow.mk
      (canonicalMap t.right (n + 1) ((F.map t.hom).toFunctor.obj X_i) (Fs t.right) ≫
        ((Sheaf.cohomologyPresheafFunctor Q.toGrothendieck (n + 1)).map
          (eqToHom (hSobj t.right).symm ≫ K.ι.app t.right)).app
            (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i))))) :
    ∀ (result : Prop),
      (∀ (Rs : ∀ j : J, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
      (ρ : ∀ {j k : J} (a : j ⟶ k),
      (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck (P k).toGrothendieck).obj (Rs j) ⟶ Rs k)
      (hρ : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
      ρ (a ≫ b) = (e a b).hom.app (Rs j) ≫
        (sheafPullback (F.map b).toFunctor AddCommGrpCat.{u}
          (P k).toGrothendieck (P l).toGrothendieck).map (ρ a) ≫ ρ b)
      (T : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
      (hTobj : ∀ j : J, T.obj j =
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (Rs j))
      (hTmap : ∀ {j k : J} (a : j ⟶ k),
      Arrow.mk (T.map a) = Arrow.mk ((eV a).hom.app (Rs j) ≫
        (sheafPullback (V.ι.app k).toFunctor AddCommGrpCat.{u}
          (P k).toGrothendieck Q.toGrothendieck).map (ρ a)))
      (L : Cocone T)
      (hL : IsColimit L)
      (E : Under i ⥤ AddCommGrpCat.{u})
      (hEobj : ∀ t : Under i,
      E.obj t = Sheaf.H' (Rs t.right) n ((F.map t.hom).toFunctor.obj X_i))
      (hEmap : ∀ {t t' : Under i} (b : t ⟶ t'),
      Arrow.mk (E.map b) = Arrow.mk
        (pullbackMap b.right n ((F.map t.hom).toFunctor.obj X_i) (Rs t.right) ≫
          ((Sheaf.cohomologyPresheafFunctor (P t'.right).toGrothendieck n).map
            (ρ b.right)).app
              (op ((F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i)))))
      (d : Cocone E)
      (hdpt : d.pt = Sheaf.H' L.pt n ((V.ι.app i).toFunctor.obj X_i))
      (hdlegs : ∀ t : Under i, Arrow.mk (d.ι.app t) = Arrow.mk
      (canonicalMap t.right n ((F.map t.hom).toFunctor.obj X_i) (Rs t.right) ≫
        ((Sheaf.cohomologyPresheafFunctor Q.toGrothendieck n).map
          (eqToHom (hTobj t.right).symm ≫ L.ι.app t.right)).app
            (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i))))) (δ : E ⟶ D)
      (Gs : ∀ j : J, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
      (ψ : ∀ {j k : J} (a : j ⟶ k),
      (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck (P k).toGrothendieck).obj (Gs j) ⟶ Gs k)
      (hψ : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
      ψ (a ≫ b) = (e a b).hom.app (Gs j) ≫
        (sheafPullback (F.map b).toFunctor AddCommGrpCat.{u}
          (P k).toGrothendieck (P l).toGrothendieck).map (ψ a) ≫ ψ b)
      (U : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
      (hUobj : ∀ j : J, U.obj j =
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (Gs j))
      (hUmap : ∀ {j k : J} (a : j ⟶ k),
      Arrow.mk (U.map a) = Arrow.mk ((eV a).hom.app (Gs j) ≫
        (sheafPullback (V.ι.app k).toFunctor AddCommGrpCat.{u}
          (P k).toGrothendieck Q.toGrothendieck).map (ψ a)))
      (M : Cocone U)
      (hM : IsColimit M)
      (B : Under i ⥤ AddCommGrpCat.{u})
      (hBobj : ∀ t : Under i,
      B.obj t = Sheaf.H' (Gs t.right) n ((F.map t.hom).toFunctor.obj X_i))
      (hBmap : ∀ {t t' : Under i} (b : t ⟶ t'),
      Arrow.mk (B.map b) = Arrow.mk
        (pullbackMap b.right n ((F.map t.hom).toFunctor.obj X_i) (Gs t.right) ≫
          ((Sheaf.cohomologyPresheafFunctor (P t'.right).toGrothendieck n).map
            (ψ b.right)).app
              (op ((F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i)))))
      (b : Cocone B)
      (hbpt : b.pt = Sheaf.H' M.pt n ((V.ι.app i).toFunctor.obj X_i))
      (hblegs : ∀ t : Under i, Arrow.mk (b.ι.app t) = Arrow.mk
      (canonicalMap t.right n ((F.map t.hom).toFunctor.obj X_i) (Gs t.right) ≫
        ((Sheaf.cohomologyPresheafFunctor Q.toGrothendieck n).map
          (eqToHom (hUobj t.right).symm ≫ M.ι.app t.right)).app
            (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i)))))
      (α : B ⟶ E) (α₀ : b.pt ⟶ d.pt) (β : d.pt ⟶ c.pt),
        (∀ t : Under i, Function.Surjective (δ.app t).hom) ∧
        (∀ t : Under i, α.app t ≫ δ.app t = 0) ∧
        (∀ t : Under i, δ.app t ≫ c.ι.app t = d.ι.app t ≫ β) ∧
        (∀ t : Under i, α.app t ≫ d.ι.app t = b.ι.app t ≫ α₀) ∧
        (∀ y : d.pt, β.hom y = 0 → ∃ w : b.pt, α₀.hom w = y) → result) → result := by
  intro result continuation
  apply cohomology_colimit_sites_short_exact_systems
    n J F P hfinite hcover hpullback V hobjects harrows Q hQ hVcover hVpullback pullbackMap
    hpullbackMap canonicalMap hcanonicalMap e he eV heV Fs φ hφ S hSobj hSmap K hK i X_i D hDobj
    hDmap c hcpt hclegs
    result
  intro Rs ρ hρ T hTobj hTmap L hL Gs ψ hψ U hUobj hUmap M hM As θ hθ pA hpA hpAV hpAD γ π hG
    hst hγ hπ f₀ g₀ w₀ h₀ hf₀ hg₀ hψid hρid
  apply cohomology_colimit_sites_boundary_diagrams
    n J F P hfinite hcover hpullback V hobjects harrows Q hQ hVcover hVpullback pullbackMap
    hpullbackMap canonicalMap hcanonicalMap e he eV heV Fs φ hφ S hSobj hSmap K hK i X_i D hDobj
    hDmap c hcpt hclegs
    Rs ρ hρ T hTobj hTmap L hL Gs ψ hψ U hUobj hUmap M hM As θ hθ pA hpA hpAV hpAD γ π hG hst hγ
    hπ f₀ g₀ w₀ h₀ hf₀ hg₀ hψid hρid
    result
  intro E hEobj hEmap d hdpt hdlegs δ B hBobj hBmap b hbpt hblegs α α₀ β hrows
  rcases hrows with ⟨hsurj, hzero, hdelta, halpha, hα₀, hβ⟩
  apply continuation
    Rs ρ hρ T hTobj hTmap L hL E hEobj hEmap d hdpt hdlegs δ Gs ψ hψ U hUobj hUmap M hM B hBobj
    hBmap b hbpt hblegs α α₀ β
  refine ⟨hsurj, hzero, hdelta, halpha, ?_⟩
  intro y hy
  have hy' : Abelian.Ext.comp ((eqToHom hdpt).hom y) h₀.extClass rfl = 0 := by
    rw [← hβ y, hy, map_zero]
  obtain ⟨z, hz⟩ := Abelian.Ext.covariant_sequence_exact₃ _ h₀
    ((eqToHom hdpt).hom y) rfl hy'
  refine ⟨(eqToHom hbpt.symm).hom z, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (eqToHom hdpt)).1
  rw [hα₀]
  simpa only [← ConcreteCategory.comp_apply, eqToHom_trans, eqToHom_refl,
    CategoryTheory.id_apply] using hz


end CategoryTheory
