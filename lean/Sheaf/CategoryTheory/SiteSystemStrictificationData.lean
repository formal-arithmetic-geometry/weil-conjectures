/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.CategoryTheory.SiteEquivalenceMorphismTransport

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Categories, construction of Tag 004A, applied fibrewise;
site transport follows `site_equivalence_morphism_transport`.
(blueprint: lem-weil-pbc-site-system-strictification-data).

Proof: at stage i take objects (j,X) with j <= i and X in C j, and define homs
using U j i X in C i. Composition and identities come from C i. Evaluation p_i
is fully faithful and essentially surjective, with quasi-inverse e_i sending X
to (i,X); normalization of U makes e_i act as the identity on homs. Define the
transition on homs by conjugating U i k with the gamma components at its two
endpoints. Naturality of gamma proves functoriality; its normalization and cocycle
prove identity and composition equalities, giving F. Take as coverings the finite
presieves whose p_i-images cover. Finite singleton isomorphisms, composites, and
pullbacks satisfy the precoverage axioms, by the corresponding axioms in P i and
the full faithfulness of p_i. Finiteness is included in the covering condition.
The equivalence e_i preserves and reflects these coverings. For any indexed
covering choose lifts once for each distinct arrow in its finite presieve, and
reuse them for repeated members of the indexed family. Fullness gives the lifted
arrows and the isomorphisms under e_i; the lifted presieve is finite and covering. The gamma
comparison intertwines evaluation and transitions; transport the covering and
pullback preservation along it. Apply site_equivalence_morphism_transport to
obtain continuity and finite limit/colimit preservation on sheaf pullbacks.
The identity of U i j X defines theta. Define v'_i(j,X)=v_j X and its arrow map
by conjugating v_i(f) with the delta components. Naturality proves it is a functor;
the normalization and cocycle of delta give the two strict equalities. Applying
v'_j to theta gives delta inverse, including both endpoints as an Arrow equality.
This constructs the strict site system, without claiming its colimit. -/
-- STATEMENT-DISPUTED: take I = WithTop ℕ, C i the one-object category, U identity,
-- and coefficients v i constant at i in Codiscrete I. The strict coefficient equalities
-- force infinitely many distinct isomorphic objects in F.obj ⊤. Indexed base change
-- of the singleton identity covering then gives an infinite covering, contradicting
-- the finiteness clause. See site_system_strictification_obstruction and report.md.
theorem exists_site_system_strictification_data
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
        (delta j k h').hom.app ((U i j h).obj X) ≫ (delta i j h).hom.app X)
    :
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
                Arrow.mk ((delta i j h).inv.app X))) := by
  sorry

end CategoryTheory
