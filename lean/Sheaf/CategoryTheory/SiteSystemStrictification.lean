/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.CategoryTheory.ColimitSites
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.CategoryTheory.SiteSystemStrictificationData
import Sheaf.CategoryTheory.FilteredColimitFunctorDescent

/-!
# Strictification of a directed system of sites

Source: Stacks Project, Categories, Lemma 004A, applied fibrewise; Sites, Situation 0A34
(blueprint: lem-weil-pbc-site-system-strictification).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Categories, Lemma 004A, and Sites, Situation 0A34.
(blueprint: lem-weil-pbc-site-system-strictification).

The site conditions are those of def-weil-pbc-sites-and-cohomology. `F` is indexed by
`I`, the filtered opposite of the cofiltered category in Situation 0A34. Equalities
in `Arrow` include endpoints and express coherence without hidden transport choices.

Proof (the node's seven steps):
1. Replace C_i by the category of pairs (j,V), j ≤ i, with morphisms the morphisms
   u_ij(V) → u_ik(W) in C_i. The functor p_i sends (j,V) to u_ij(V); e_i sends V to
   (i,V). Their composites are naturally isomorphic to the identities.
2. Give this category the finite covering families whose p_i-images cover. Pullbacks,
   composition and singleton isomorphisms satisfy the site axioms. The equivalence
   preserves and reflects coverings, and each covering is isomorphic to an image.
3. The new transition functor fixes (j,V) and sends f to gamma_ik followed by u(f)
   followed by gamma_ij inverse (in diagrammatic order, inverse first). Naturality
   and the cocycle identity give strict identities and strict composition.
4. The identity of u_ki(V) gives theta : e_i u'_ki ≅ u_ki e_k. The gamma components
   also compare p_i u_ki with u'_ki p_k.
5. Apply lem-weil-pbc-site-equivalence-morphism-transport to p_i and p_k and this
   comparison: the new transition is continuous and defines a morphism of sites.
6. Set v'_i(j,V)=v_j(V), conjugating v_i(f) by delta. Normalization gives e_i v'_i=v_i;
   the delta cocycle and naturality give u'_ki v'_k=v'_i and v'_k(theta)=delta inverse.
7. The strict system satisfies Situation 0A34. Apply lem-weil-pbc-colimit-of-sites
   and lem-weil-pbc-filtered-colimit-categories. Compatible object and arrow maps
   descend to their set colimits (def-weil-pbc-category-colimit). Composition and
   identities can be checked at a common stage, giving the asserted functor V. -/
theorem exists_site_system_strictification
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (C : I → Cat.{u, u}) (P : ∀ i : I, Precoverage (C i))
    [∀ i, (P i).HasIsos] [∀ i, (P i).IsStableUnderComposition]
    [∀ i, (P i).IsStableUnderBaseChange] [∀ i, (P i).HasPullbacks]
    (hfinite : ∀ (i : I) (X : C i) (R : Presieve X), R ∈ P i X → Finite R.uncurry)
    (U : ∀ (i j : I), i ≤ j → C i ⥤ C j)
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X)
    (hcover : ∀ (i j : I) (h : i ≤ j) (X : C i) (R : Presieve X),
      R ∈ P i X → R.map (U i j h) ∈ P j ((U i j h).obj X))
    (hpullback : ∀ (i j : I) (h : i ≤ j) (X Y Z : C i) (R : Presieve X),
      R ∈ P i X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (U i j h))
    [∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
      (P i).toGrothendieck (P j).toGrothendieck]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteLimits
      (sheafPullback (U i j h) (Type u) (P i).toGrothendieck (P j).toGrothendieck)]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteColimits
      (sheafPullback (U i j h) (Type u) (P i).toGrothendieck (P j).toGrothendieck)]
    (D : Type v) [Category.{w} D] (v : ∀ i : I, C i ⥤ D)
    (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
    (hdelta : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
      (v k).map ((gamma i j k h h').hom.app X) ≫
          (delta i k (h.trans h')).hom.app X =
        (delta j k h').hom.app ((U i j h).obj X) ≫ (delta i j h).hom.app X) :
    ∃ (F : I ⥤ Cat.{u, u}) (Q : ∀ i : I, Precoverage (F.obj i))
      (e : ∀ i : I, C i ⥤ F.obj i),
      (∀ i : I, (e i).IsEquivalence) ∧
      (∃ (_ : ∀ i, (Q i).HasIsos) (_ : ∀ i, (Q i).IsStableUnderComposition)
        (_ : ∀ i, (Q i).IsStableUnderBaseChange) (_ : ∀ i, (Q i).HasPullbacks),
        (∀ (i : I) (X : F.obj i) (R : Presieve X), R ∈ Q i X → Finite R.uncurry) ∧
        (∀ (i : I) (X : C i) (R : Presieve X),
          R ∈ P i X ↔ R.map (e i) ∈ Q i ((e i).obj X)) ∧
        (∀ (i : I) (X : F.obj i) (K : Type u) (A : K → F.obj i)
          (f : ∀ a : K, A a ⟶ X), Presieve.ofArrows A f ∈ Q i X →
          ∃ (Y : C i) (B : K → C i) (g : ∀ a : K, B a ⟶ Y)
            (t : (e i).obj Y ≅ X) (s : ∀ a : K, (e i).obj (B a) ≅ A a),
            Presieve.ofArrows B g ∈ P i Y ∧
              ∀ a : K, (e i).map (g a) ≫ t.hom = (s a).hom ≫ f a) ∧
        (∀ (i j : I) (h : i ≤ j) (X : F.obj i) (R : Presieve X), R ∈ Q i X →
          R.map (F.map (homOfLE h)).toFunctor ∈
            Q j ((F.map (homOfLE h)).toFunctor.obj X)) ∧
        (∀ (i j : I) (h : i ≤ j) (X Y Z : F.obj i) (R : Presieve X), R ∈ Q i X →
          ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
            PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor) ∧
        ∃ (_ : ∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor.IsContinuous
            (Q i).toGrothendieck (Q j).toGrothendieck),
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteLimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteColimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          ∃ (theta : ∀ (i j : I) (h : i ≤ j),
              e i ⋙ (F.map (homOfLE h)).toFunctor ≅ U i j h ⋙ e j)
            (v' : ∀ i : I, F.obj i ⥤ D),
            (∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i) ∧
            (∀ i : I, e i ⋙ v' i = v i) ∧
            (∀ (i j : I) (h : i ≤ j) (X : C i),
              Arrow.mk ((v' j).map ((theta i j h).hom.app X)) =
                Arrow.mk ((delta i j h).inv.app X)) ∧
            ∃ (L : Cocone F) (V : L.pt ⥤ D),
              Nonempty (IsColimit (Cat.objects.mapCocone L)) ∧
              Nonempty (IsColimit (Cat.arrows.mapCocone L)) ∧
              ∀ i : I, (L.ι.app i).toFunctor ⋙ V = v' i) := by
  obtain ⟨F, Q, e, he, hQ⟩ := exists_site_system_strictification_data
    (I := I) (C := C) (P := P) (hfinite := hfinite) (U := U) (hUid := hUid)
    (gamma := gamma) (hgammaLeft := hgammaLeft) (hgammaRight := hgammaRight)
    (hgamma := hgamma) (hcover := hcover) (hpullback := hpullback)
    (D := D) (v := v) (delta := delta) (hdeltaId := hdeltaId) (hdelta := hdelta)
  obtain ⟨hiso, hcomp, hbase, hpull, hfin, hecover, heimage, hcov, hpb, hcont,
    hlim, hcolim, theta, v', hvcompat, hecompat, htheta⟩ := hQ
  let := hiso
  let := hcomp
  let := hbase
  let := hpull
  have hcov' : ∀ (i j : I) (a : i ⟶ j) (X : F.obj i) (R : Presieve X),
      R ∈ Q i X → R.map (F.map a).toFunctor ∈ Q j ((F.map a).toFunctor.obj X) := by
    intro i j a
    have ha : a = homOfLE (leOfHom a) := Subsingleton.elim _ _
    rw [ha]
    exact hcov i j (leOfHom a)
  have hpb' : ∀ (i j : I) (a : i ⟶ j) (X Y Z : F.obj i) (R : Presieve X),
      R ∈ Q i X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor := by
    intro i j a
    have ha : a = homOfLE (leOfHom a) := Subsingleton.elim _ _
    rw [ha]
    exact hpb i j (leOfHom a)
  let : ∀ (i j : I) (a : i ⟶ j), (F.map a).toFunctor.IsContinuous
      (Q i).toGrothendieck (Q j).toGrothendieck := by
    intro i j a
    have ha : a = homOfLE (leOfHom a) := Subsingleton.elim _ _
    rw [ha]
    exact hcont i j (leOfHom a)
  let : ∀ (i j : I) (a : i ⟶ j), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (Q i).toGrothendieck (Q j).toGrothendieck) := by
    intro i j a
    have ha : a = homOfLE (leOfHom a) := Subsingleton.elim _ _
    rw [ha]
    exact (hlim i j (leOfHom a)).some
  let : ∀ (i j : I) (a : i ⟶ j), PreservesFiniteColimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (Q i).toGrothendieck (Q j).toGrothendieck) := by
    intro i j a
    have ha : a = homOfLE (leOfHom a) := Subsingleton.elim _ _
    rw [ha]
    exact (hcolim i j (leOfHom a)).some
  obtain ⟨L, hobjects, harrows, _⟩ := exists_colimit_site I F Q hfin hcov' hpb'
  have hvcompat' : ∀ (i j : I) (a : i ⟶ j), (F.map a).toFunctor ⋙ v' j = v' i := by
    intro i j a
    have ha : a = homOfLE (leOfHom a) := Subsingleton.elim _ _
    rw [ha]
    exact hvcompat i j (leOfHom a)
  obtain ⟨V, hV⟩ := exists_filteredColimit_functor_descent I F L hobjects harrows D v'
    hvcompat'
  exact ⟨F, Q, e, he, hiso, hcomp, hbase, hpull, hfin, hecover, heimage, hcov, hpb,
    hcont, hlim, hcolim, theta, v', hvcompat, hecompat, htheta, L, V,
    hobjects, harrows, hV⟩

end CategoryTheory
