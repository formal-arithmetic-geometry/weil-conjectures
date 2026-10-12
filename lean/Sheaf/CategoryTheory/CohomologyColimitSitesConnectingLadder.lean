/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.CategoryTheory.ColimitSites
public import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.ColimitSitesAcyclicReplacement
import Sheaf.CategoryTheory.ColimitSitesCohomologyDiagram
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # A connecting-map ladder for colimit-site cohomology.

Source: Stacks Project, Tags 09YP, 0739 and 09YN.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem hom_eq_of_arrow_eq {C : Type*} [Category C]
    {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    (h : Arrow.mk f = Arrow.mk g) (hA : A = A') (hB : B = B') :
    f = eqToHom hA ≫ g ≫ eqToHom hB.symm := by
  obtain ⟨hA', hB', hg⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  exact hg

private theorem transport_ladder {C : Type*} [Category C]
    {A A' Ar Ar' B B' Br Br' T T' : C}
    (l : A ⟶ T) (r : A' ⟶ T') (ll : Ar ⟶ Br) (rr : Ar' ⟶ Br')
    (β : Ar' ⟶ Ar) (d : B' ⟶ B)
    (hA : A = Ar) (hA' : A' = Ar') (hT : T = B) (hT' : T' = B')
    (hU : Br = B) (hU' : Br' = B')
    (hl : Arrow.mk l = Arrow.mk ll) (hr : Arrow.mk r = Arrow.mk rr)
    (hb : β ≫ ll ≫ eqToHom hU = rr ≫ eqToHom hU' ≫ d) :
    (eqToHom hA' ≫ β ≫ eqToHom hA.symm) ≫ l =
      r ≫ (eqToHom hT' ≫ d ≫ eqToHom hT.symm) := by
  have hl' := hom_eq_of_arrow_eq l ll hl hA (hT.trans hU.symm)
  have hr' := hom_eq_of_arrow_eq r rr hr hA' (hT'.trans hU'.symm)
  rw [hl', hr']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simpa only [Category.assoc, eqToHom_trans] using
    congrArg (fun z ↦ eqToHom hA' ≫ z ≫ eqToHom hT.symm) hb

-- Retain the named existential proof witnesses in the unchanged signature.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
/-- A positive-degree comparison admits a lower-degree connecting-map ladder.
The returned system is a cokernel of a compatible injective embedding after
normalizing any idempotent identity transitions.
The target connecting homomorphism is surjective, and every stage connecting
homomorphism commutes with its comparison leg. No descent assertion for the
returned lower-degree diagram is assumed or asserted.

Source: Stacks Project, Cohomology on Sites, Tag 09YP, second and third paragraphs,
and the short exact sequences and diagram of Tag 0739; Tag 0EXZ supplies the embedding
(https://stacks.math.columbia.edu/tag/09YP).
(blueprint: lem-weil-pbc-colimit-sites-connecting-ladder).

Proof:
1. Identify identity inverse image with the identity functor using its adjunction
   unit. The cocycle makes each identity coefficient action an idempotent. Split it
   in the abelian sheaf category and restrict transitions to its image; the resulting
   system has identity transitions. Exact inverse image preserves this splitting.
   The identity law of `S`, together with `hSmap`, says the pulled-back idempotent
   is the identity, so the normalized inverse-image diagram is isomorphic to `S`.
   Similarly `hDmap` and the identity law of `D` say the idempotent acts identically
   on the specified degree-(n+1) stage groups; the normalized inclusions induce
   isomorphisms onto those groups. Transpose the normalized transitions through
   adjunctions. Their cocycle follows from `hφ` and unit coherence `he`. Apply the
   compatible injective-system theorem (0EXZ), and transpose back to obtain
   compatible monomorphisms from the normalized coefficients into `Gs j`.
2. Set `FsR j` to their cokernels. Exact inverse image transports these cokernels;
   compatibility of the embeddings gives `φR`. Cancel the cokernel epimorphisms to
   check `hφR`. Form the inverse-image diagram `SR`, with `hSobjR`, `hSmapR`, and
   its colimit `KR`. Exact inverse image and exact filtered colimits give a short
   exact sequence `0 → K.pt → G → KR.pt → 0`, using the normalized colimit
   identification from step 1.
3. Every covering of the colimit site descends by `hQ`. It is finite, and the Cech
   comparison identifies the Cech complex of `G` with a filtered colimit of the
   stage injective Cech complexes. They are positively acyclic by 03AW. Exact
   filtered colimits preserve this, and the Cech vanishing criterion 03F9 gives
   `H' G (n+1) U = 0` for every object `U`.
4. Form the degree-n stage diagram `DR` of the cokernel system. Naturality of
   `pullbackMap`, and its compatibility with connecting maps, give its functor laws
   from the corresponding laws for actual site pullback. The latter agree with the
   supplied maps: naturality and connecting compatibility determine them uniquely
   from degree zero, by injective dimension shifting. Similarly form `cR` using the
   canonical maps and the coprojections of `KR`; record its object and leg equations.
5. The long exact sequence for the short exact sequence in step 2 gives the target
   connecting map `δ : cR.pt → c.pt`. Its next term is zero by step 3, so `δ` is
   surjective. At each stage the long exact sequence supplies the boundary into
   the normalized coefficient system. Follow it by the normalized inclusion on
   cohomology to obtain `δstage t` with the original endpoint `D.obj t`.
6. The connecting-map clauses of `hpullbackMap` and `hcanonicalMap`, together with
   naturality in the compatible short exact sequences and their colimit, give the
   square `δstage t ≫ c_t = cR_t ≫ δ`. Transport endpoints with the specified object
   equalities. This constructs the ladder without any induction hypothesis.
-/
theorem cohomology_colimit_sites_connecting_ladder
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
    (DR : Under i ⥤ AddCommGrpCat.{u})
    (hDobjR : ∀ t : Under i,
      DR.obj t = Sheaf.H' (FsR t.right) n ((F.map t.hom).toFunctor.obj X_i))
    (hDmapR : ∀ {t t' : Under i} (b : t ⟶ t'),
      Arrow.mk (DR.map b) = Arrow.mk
        (pullbackMap b.right n ((F.map t.hom).toFunctor.obj X_i) (FsR t.right) ≫
          ((Sheaf.cohomologyPresheafFunctor (P t'.right).toGrothendieck n).map
            (φR b.right)).app
              (op ((F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i)))))
    (cR : Cocone DR)
    (hcptR : cR.pt = Sheaf.H' KR.pt n ((V.ι.app i).toFunctor.obj X_i))
    (hclegsR : ∀ t : Under i, Arrow.mk (cR.ι.app t) = Arrow.mk
      (canonicalMap t.right n ((F.map t.hom).toFunctor.obj X_i) (FsR t.right) ≫
        ((Sheaf.cohomologyPresheafFunctor Q.toGrothendieck n).map
          (eqToHom (hSobjR t.right).symm ≫ KR.ι.app t.right)).app
            (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i))))),
      ∃ (δ : cR.pt ⟶ c.pt) (δstage : ∀ t : Under i, DR.obj t ⟶ D.obj t),
        Function.Surjective δ.hom ∧
        (∀ t : Under i, δstage t ≫ c.ι.app t = cR.ι.app t ≫ δ) := by
  classical
  have hU (t : Under i) :
      (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X_i) =
        (V.ι.app i).toFunctor.obj X_i := by
    exact congrArg (fun a : F.obj i ⟶ V.pt ↦ a.toFunctor.obj X_i) (V.w t.hom)
  obtain ⟨FsR, φR, hφR, SR, hSobjR, hSmapR, KR, hKR, hidR,
      G, f, g, w, hE, d, hdformula, hG, β, hβ⟩ :=
    colimit_sites_acyclic_replacement J F P hfinite hcover hpullback V hobjects harrows Q hQ hVcover
      hVpullback @pullbackMap @hpullbackMap canonicalMap hcanonicalMap @e @he @eV @heV
      Fs @φ @hφ S hSobj @hSmap K hK i X_i n hU
  obtain ⟨DR, hDobjR, hDmapR, cR, hcptR, hclegsR⟩ :=
    colimit_sites_cohomology_diagram J F P hcover hpullback V Q hVcover
      hVpullback @pullbackMap @hpullbackMap canonicalMap hcanonicalMap @e @he @eV @heV
      FsR @φR @hφR SR hSobjR @hSmapR KR i X_i n hidR
  have hd : Function.Surjective d.hom := by
    intro x
    have hz := hG ((V.ι.app i).toFunctor.obj X_i) (n + 1) (Nat.zero_lt_succ n)
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hE x
      ((AddCommGrpCat.subsingleton_of_isZero hz).elim _ _) rfl
    exact ⟨y, (hdformula y).trans hy⟩
  let δ : cR.pt ⟶ c.pt := eqToHom hcptR ≫ d ≫ eqToHom hcpt.symm
  let δstage (t : Under i) : DR.obj t ⟶ D.obj t :=
    eqToHom (hDobjR t) ≫ β t ≫ eqToHom (hDobj t).symm
  refine ⟨FsR, @φR, @hφR, SR, hSobjR, @hSmapR, KR, hKR, DR, hDobjR,
    @hDmapR, cR, hcptR, hclegsR, δ, δstage, ?_, ?_⟩
  · have : IsIso (eqToHom hcptR) := inferInstance
    have : IsIso (eqToHom hcpt.symm) := inferInstance
    exact ((AddCommGrpCat.epi_iff_surjective δ).mp (by
      have : Epi d := (AddCommGrpCat.epi_iff_surjective d).mpr hd
      dsimp [δ]
      infer_instance))
  · intro t
    exact transport_ladder (c.ι.app t) (cR.ι.app t) _ _ (β t) d
      (hDobj t) (hDobjR t) hcpt hcptR
      (congrArg (Sheaf.H' K.pt (n + 1)) (hU t))
      (congrArg (Sheaf.H' KR.pt n) (hU t)) (hclegs t) (hclegsR t) (hβ t)

end CategoryTheory
