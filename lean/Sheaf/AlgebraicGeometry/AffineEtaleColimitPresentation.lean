/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
public import Mathlib.CategoryTheory.Category.Cat
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.Pullback
import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
import Sheaf.CategoryTheory.ColimitSites
import Sheaf.CategoryTheory.FilteredColimitCategories
import Sheaf.CategoryTheory.SiteEquivalenceMorphismTransport
import Sheaf.CategoryTheory.SiteSystemStrictification

/-!
# AffineEtaleColimitPresentation

Source: Stacks Project, Étale Cohomology 0EYL; Sites 09YL.
(blueprint: lem-weil-pbc-affine-etale-colimit-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Categories 004A; Sites 0A34 and 09YL;
Étale Cohomology 0EYL, qcqs case.

Proof (steps 4 and 8 of lem-weil-pbc-affine-etale-site-colimit):
1. Strictify the coherent system using pairs (j,A) with j ≤ i at stage i. Morphisms
   are maps between their U-images in the affine site at i. The comparison functor to
   that site is an equivalence with quasi-inverse e_i. Transition fixes the pair and
   conjugates the image of a morphism by gamma. The gamma cocycle gives strict
   composition. Give the new category the precoverage detected by the equivalence.
   Its site axioms and finiteness follow from the original finite étale precoverage.
2. Define v'_i(j,A) = v_j(A), conjugating morphisms by delta. The delta cocycle gives
   strict compatibility with transition, and normalization gives eta. The theta
   comparison satisfies the displayed Arrow equation. Equivalence transports all
   pullbacks, covering preservation, continuity, adjunctions, and finite-limit
   preservation. This construction uses Cat.{u, u + 1}: the original sites have
   object universe u + 1 and morphism universe u; coefficients remain Type u.
3. Form filtered colimits of the object and arrow sets. Source, target, identities
   and composition descend because any finite collection of data occurs at a common
   stage and any equality holds eventually. These operations give K; compatibility
   of v' gives W. The union of images of stage precoverages is P (09YL).
4. Object descent makes W essentially surjective. Map descent makes it full and
   eventual equality makes it faithful, after representing any two objects at a
   common stage. Thus W is an equivalence.
5. Images of stage covers cover by preservation. For reflection, represent the
   finite presieve at a stage. Descent of covers presents its W-image as a stage
   cover; map descent and eventual equality align these two finite presentations
   at a common later stage. Invariance under isomorphism then identifies the original
   presieve with an image of a stage cover. This gives the asserted iff and site axioms.
(blueprint: lem-weil-pbc-affine-etale-colimit-presentation). -/
-- STATEMENT-DISPUTED: finite covering presieves are incompatible with the asserted
-- IsStableUnderComposition and cover-preserving equivalences. For a singleton index
-- and identity system over a field, each fold map from n+1 copies of Spec(k) covers.
-- Repeat the identity cover with index Nat and refine its nth copy by this singleton
-- fold cover. IsStableUnderComposition makes their infinite union cover, whereas
-- the conclusion requires it to be finite. Equivalence keeps the pairwise
-- nonisomorphic source objects distinct. Mathlib's finite Pretopology satisfies
-- the weaker presieve-bind transitivity, not this arbitrary-family composition axiom.
theorem exists_affineEtale_colimit_presentation
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c)
    (U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
          (D.obj (op j)).FullAffineEtale)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
      (p : ∀ (i j : I) (h : i ≤ j),
        U i j h ⋙ fullAffineEtaleInclusion (D.obj (op j)) ⋙
          Etale.forget (D.obj (op j)) ⋙ Over.forget (D.obj (op j)) ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (q : ∀ i : I,
        v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
        U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
      (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)
    (h0 : (∀ i : I, U i i le_rfl = 𝟭 _))
    (h3 : (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i i k le_rfl h) (Iso.refl (U i k h))))
    (h4 : (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i k k h le_rfl) (Iso.refl (U i k h))))
    (h5 : (∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i))))
    (h8 : (∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l)
        (A : (D.obj (op i)).FullAffineEtale),
        (gamma j k l h' h'').hom.app ((U i j h).obj A) ≫
            (gamma i j l h (h'.trans h'')).hom.app A =
          (U k l h'').map ((gamma i j k h h').hom.app A) ≫
            (gamma i k l (h.trans h') h'').hom.app A))
    (h9 : (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        (v k).map ((gamma i j k h h').hom.app A) ≫
            (delta i k (h.trans h')).hom.app A =
          (delta j k h').hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A))
    (h10 : (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (U i j h) ∈ fullAffineEtalePrecoverage (D.obj (op j)) ((U i j h).obj A)))
    (h11 : (∀ (i j : I) (h : i ≤ j) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (U i j h)))
    (h12 : (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (v i) ∈ fullAffineEtalePrecoverage c.pt ((v i).obj A)))
    (h13 : (∀ (i : I) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (v i)))
    (h14 : (∃ (_ : ∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology (D.obj (op j))))
        (_ : ∀ i : I, (v i).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology c.pt)),
        (∀ (i j : I) (h : i ≤ j), ∃ L :
            Sheaf (fullAffineEtaleTopology (D.obj (op i))) (Type u) ⥤
              Sheaf (fullAffineEtaleTopology (D.obj (op j))) (Type u),
          Nonempty (L ⊣ (U i j h).sheafPushforwardContinuous (Type u)
            (fullAffineEtaleTopology (D.obj (op i)))
            (fullAffineEtaleTopology (D.obj (op j)))) ∧ PreservesFiniteLimits L) ∧
        (∀ i : I, ∃ L : Sheaf (fullAffineEtaleTopology (D.obj (op i))) (Type u) ⥤
            Sheaf (fullAffineEtaleTopology c.pt) (Type u),
          Nonempty (L ⊣ (v i).sheafPushforwardContinuous (Type u)
            (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology c.pt)) ∧
          PreservesFiniteLimits L)))
    (h15 : (∀ A : c.pt.FullAffineEtale,
        ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale), Nonempty ((v i).obj Ai ≅ A)))
    (h16 : (∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale)
        (f : (v i).obj A ⟶ (v i).obj B),
        ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
          f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B))
    (h17 : (∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale) (f g : A ⟶ B),
        (v i).map f = (v i).map g →
          ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g))
    (h18 : (∀ (n : ℕ) (A : c.pt.FullAffineEtale) (B : Fin n → c.pt.FullAffineEtale)
        (f : ∀ a : Fin n, B a ⟶ A),
        Presieve.ofArrows B f ∈ fullAffineEtalePrecoverage c.pt A ↔
          ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale)
            (Bi : Fin n → (D.obj (op i)).FullAffineEtale) (fi : ∀ a : Fin n, Bi a ⟶ Ai)
            (t : (v i).obj Ai ≅ A) (s : ∀ a : Fin n, (v i).obj (Bi a) ≅ B a),
            Presieve.ofArrows Bi fi ∈ fullAffineEtalePrecoverage (D.obj (op i)) Ai ∧
              ∀ a : Fin n, (v i).map (fi a) ≫ t.hom = (s a).hom ≫ f a))
    :
      ∃ (F : I ⥤ Cat.{u, u + 1}) (Q : ∀ i : I, Precoverage (F.obj i))
        (e : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ F.obj i)
        (v' : ∀ i : I, F.obj i ⥤ c.pt.FullAffineEtale)
        (theta : ∀ (i j : I) (h : i ≤ j),
          e i ⋙ (F.map (homOfLE h)).toFunctor ≅ U i j h ⋙ e j)
        (eta : ∀ i : I, e i ⋙ v' i ≅ v i),
        (∀ i : I, (e i).IsEquivalence) ∧ (∃ (_ : ∀ i : I, (Q i).HasIsos)
          (_ : ∀ i : I, (Q i).IsStableUnderComposition)
          (_ : ∀ i : I, (Q i).IsStableUnderBaseChange)
          (_ : ∀ i : I, (Q i).HasPullbacks),
          (∀ (i : I) (A : F.obj i) (R : Presieve A), R ∈ Q i A → Finite R.uncurry) ∧
          (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
            R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A ↔
              R.map (e i) ∈ Q i ((e i).obj A)) ∧
          (∀ (i j : I) (h : i ≤ j) (A : F.obj i) (R : Presieve A), R ∈ Q i A →
            R.map (F.map (homOfLE h)).toFunctor ∈
              Q j ((F.map (homOfLE h)).toFunctor.obj A)) ∧
          (∀ (i j : I) (h : i ≤ j) (A B C : F.obj i) (f : B ⟶ A) (g : C ⟶ A),
            PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor) ∧
          (∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i) ∧
          (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
            Arrow.mk ((v' j).map ((theta i j h).hom.app A) ≫
                (eta j).hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A) =
              Arrow.mk ((eta i).hom.app A)) ∧
          (∃ (_ : ∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor.IsContinuous
              (Q i).toGrothendieck (Q j).toGrothendieck)
            (_ : ∀ i : I, (v' i).IsContinuous (Q i).toGrothendieck
              (fullAffineEtaleTopology c.pt)),
            (∀ (i j : I) (h : i ≤ j), ∃ L : Sheaf (Q i).toGrothendieck (Type u) ⥤
                Sheaf (Q j).toGrothendieck (Type u),
              Nonempty (L ⊣ (F.map (homOfLE h)).toFunctor.sheafPushforwardContinuous
                (Type u) (Q i).toGrothendieck (Q j).toGrothendieck) ∧
                PreservesFiniteLimits L) ∧
            (∀ i : I, ∃ L : Sheaf (Q i).toGrothendieck (Type u) ⥤
                Sheaf (fullAffineEtaleTopology c.pt) (Type u),
              Nonempty (L ⊣ (v' i).sheafPushforwardContinuous (Type u)
                (Q i).toGrothendieck (fullAffineEtaleTopology c.pt)) ∧
                PreservesFiniteLimits L)) ∧
          ∃ (K : Cocone F) (W : K.pt ⥤ c.pt.FullAffineEtale) (P : Precoverage K.pt),
            Nonempty (IsColimit (Cat.objects.mapCocone K)) ∧
            Nonempty (IsColimit (Cat.arrows.mapCocone K)) ∧
            (∀ i : I, (K.ι.app i).toFunctor ⋙ W = v' i) ∧
            (∀ (A : K.pt) (R : Presieve A), R ∈ P A ↔
              ∃ (i : I) (Ai : F.obj i) (Ri : Presieve Ai)
                (h : (K.ι.app i).toFunctor.obj Ai = A),
                Ri ∈ Q i Ai ∧ h ▸ Ri.map (K.ι.app i).toFunctor = R) ∧
            (∃ (_ : P.HasIsos) (_ : P.IsStableUnderComposition)
              (_ : P.IsStableUnderBaseChange) (_ : P.HasPullbacks),
              W.IsEquivalence ∧ ∀ (A : K.pt) (R : Presieve A),
                R ∈ P A ↔ R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A))) := by sorry

end AlgebraicGeometry.Scheme
