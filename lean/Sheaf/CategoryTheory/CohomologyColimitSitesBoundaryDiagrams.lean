/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.CategoryTheory.ColimitSites
public import Sheaf.CategoryTheory.SiteCohomologyPullback

/-! # Cohomology boundary diagrams from short exact systems -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Assemble cohomology diagrams and comparison squares from compatible short exact systems.
This construction does not assert target kernel-image exactness.
Source: Stacks Project, Tags 09YP and 0739 (the two-row cohomology diagram).
(blueprint: lem-weil-pbc-colimit-sites-boundary-diagrams).

Proof: use uniqueness of the cohomological pullback maps from their degree-zero unit
formula, coefficient naturality, and connecting compatibility to identify the supplied
maps with the canonical ones. Composition and the coefficient cocycles define the
functors E and B on Under i. Form their canonical cocones by pullback followed by the
colimit legs; transport the endpoints by the given object equations. Define delta by
the stage connecting homomorphisms and alpha by the stage quotient maps. Connecting
naturality proves both natural transformation laws.
Transport the stage boundary along the inverse of the degree n+1 map induced by pA.
The equations hpAV and hpAD ensure this transport agrees with the supplied endpoints.
The normalized identity conditions hψid and hρid supply the functor identity laws.
Stage short exactness proves
alpha followed by delta is zero. Injectivity of each middle term gives vanishing in
degree n+1, hence surjectivity of each delta. At the target, define alpha0 by the map
g0 and beta by the extension class of the supplied short exact sequence. Coefficient
naturality and connecting compatibility of the canonical maps give both squares.
The final two equations record these actual definitions after endpoint transport. -/
theorem cohomology_colimit_sites_boundary_diagrams (n : ℕ)
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
            (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i)))))
    (Rs : ∀ j : J, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
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
      (As : ∀ j : J, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
      (θ : ∀ {j k : J} (a : j ⟶ k),
        (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck (P k).toGrothendieck).obj (As j) ⟶ As k)
      (hθ : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
        θ (a ≫ b) = (e a b).hom.app (As j) ≫
          (sheafPullback (F.map b).toFunctor AddCommGrpCat.{u}
            (P k).toGrothendieck (P l).toGrothendieck).map (θ a) ≫ θ b)
      (pA : ∀ j : J, Fs j ⟶ As j)
      (hpA : ∀ {j k : J} (a : j ⟶ k), φ a ≫ pA k =
        (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck (P k).toGrothendieck).map (pA j) ≫ θ a)
      (hpAV : ∀ j : J, IsIso
        ((sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck Q.toGrothendieck).map (pA j)))
      (hpAD : ∀ t : Under i, IsIso
        (((Sheaf.cohomologyPresheafFunctor (P t.right).toGrothendieck (n + 1)).map
          (pA t.right)).app (op ((F.map t.hom).toFunctor.obj X_i))))
      (γ : ∀ j : J, As j ⟶ Gs j)
      (π : ∀ j : J, Gs j ⟶ Rs j)
      (hG : ∀ j : J, Injective (Gs j))
      (hst : ∀ j : J, ∃ w : γ j ≫ π j = 0,
        (ShortComplex.mk (γ j) (π j) w).ShortExact)
      (hγ : ∀ {j k : J} (a : j ⟶ k), θ a ≫ γ k =
        (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck (P k).toGrothendieck).map (γ j) ≫ ψ a)
      (hπ : ∀ {j k : J} (a : j ⟶ k), ψ a ≫ π k =
        (sheafPullback (F.map a).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck (P k).toGrothendieck).map (π j) ≫ ρ a)
      (f₀ : K.pt ⟶ M.pt) (g₀ : M.pt ⟶ L.pt) (w₀ : f₀ ≫ g₀ = 0)
      (h₀ : (ShortComplex.mk f₀ g₀ w₀).ShortExact)
      (hf₀ : ∀ j : J, K.ι.app j ≫ f₀ =
        eqToHom (hSobj j) ≫
          (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
            (P j).toGrothendieck Q.toGrothendieck).map (pA j ≫ γ j) ≫
          eqToHom (hUobj j).symm ≫ M.ι.app j)
      (hg₀ : ∀ j : J, M.ι.app j ≫ g₀ =
        eqToHom (hUobj j) ≫
          (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
            (P j).toGrothendieck Q.toGrothendieck).map (π j) ≫
          eqToHom (hTobj j).symm ≫ L.ι.app j)
      (hψid : ∀ (j : J) (q : ℕ) (X : F.obj j),
        Arrow.mk (pullbackMap (𝟙 j) q X (Gs j) ≫
          ((Sheaf.cohomologyPresheafFunctor (P j).toGrothendieck q).map
            (ψ (𝟙 j))).app (op ((F.map (𝟙 j)).toFunctor.obj X))) =
          Arrow.mk (𝟙 (Sheaf.H' (Gs j) q X)))
      (hρid : ∀ (j : J) (q : ℕ) (X : F.obj j),
        Arrow.mk (pullbackMap (𝟙 j) q X (Rs j) ≫
          ((Sheaf.cohomologyPresheafFunctor (P j).toGrothendieck q).map
            (ρ (𝟙 j))).app (op ((F.map (𝟙 j)).toFunctor.obj X))) =
          Arrow.mk (𝟙 (Sheaf.H' (Rs j) q X)))
 :
    ∀ result : Prop,
      (∀ (E : Under i ⥤ AddCommGrpCat.{u})
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
        (∀ x : b.pt, (eqToHom hdpt).hom (α₀.hom x) =
          Abelian.Ext.comp ((eqToHom hbpt).hom x) (Abelian.Ext.mk₀ g₀) (add_zero n)) ∧
        (∀ y : d.pt, (eqToHom hcpt).hom (β.hom y) =
          Abelian.Ext.comp ((eqToHom hdpt).hom y) h₀.extClass rfl) → result) → result := by sorry

end CategoryTheory
