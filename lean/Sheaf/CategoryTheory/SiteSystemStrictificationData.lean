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
public import WeilConjectures.CategoryTheory.FinitePrecoverage
import Sheaf.CategoryTheory.SiteSystemStrictificationCategory
import Sheaf.CategoryTheory.SiteSystemFiniteSheafTransport

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Categories, construction of Tag 004A, applied fibrewise;
site transport uses finite covering axioms and the adjunction API of Mathlib.
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
pullback preservation along it. Use the finite pairwise-pullback sheaf criterion for
continuity. Evaluation and
its section induce inverse pushforwards on sheaves; compose their pullback adjunctions
with those of U and use uniqueness of left adjoints for finite-limit/colimit preservation.
The identity of U i j X defines theta. Define v'_i(j,X)=v_j X and its arrow map
by conjugating v_i(f) with the delta components. Naturality proves it is a functor;
the normalization and cocycle of delta give the two strict equalities. Applying
v'_j to theta gives delta inverse, including both endpoints as an Arrow equality.
This constructs the strict site system, without claiming its colimit. -/
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
      (∃ (_ : ∀ i, (Q i).HasIsos) (_ : ∀ i, (Q i).IsStableUnderFiniteComposition)
        (_ : ∀ i, (Q i).IsStableUnderFiniteBaseChange) (_ : ∀ i, (Q i).HasPullbacks),
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
  let F := SiteSystemPairs.diagram C U gamma hUid hgammaRight hgamma
  let p := SiteSystemPairs.eval C U
  let e := SiteSystemPairs.inclusion C U
  let Q := fun i => finiteEquivalencePrecoverage (p i) (P i)
  have hp (i : I) : (p i).IsEquivalence :=
    SiteSystemPairs.eval_isEquivalence C U hUid i
  have he (i : I) : (e i).IsEquivalence :=
    SiteSystemPairs.inclusion_isEquivalence C U hUid i
  have hep (i : I) : e i ⋙ p i = 𝟭 (C i) :=
    (SiteSystemPairs.inclusion_eval C U i).trans (hUid i)
  have hcov (i j : I) (h : i ≤ j) (X : F.obj i) (R : Presieve X)
      (hR : R ∈ Q i X) :
      R.map (F.map (homOfLE h)).toFunctor ∈ Q j
        ((F.map (homOfLE h)).toFunctor.obj X) :=
    finiteEquivalencePrecoverage_transition (p i) (P i) (p j) (P j)
      (U i j h) (hcover i j h) (SiteSystemPairs.transition C U gamma i j h)
      (SiteSystemPairs.comparison C U gamma i j h) X R hR
  have hpb (i j : I) (h : i ≤ j) (X Y Z : F.obj i) (R : Presieve X)
      (hR : R ∈ Q i X) (f : Y ⟶ X) (g : Z ⟶ X) (hf : R f) :
      PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor :=
    finiteEquivalencePrecoverage_transition_pullback (p i) (P i) (p j) (U i j h)
      (hpullback i j h) (SiteSystemPairs.transition C U gamma i j h)
      (SiteSystemPairs.comparison C U gamma i j h) X Y Z R hR f g hf
  have hcont (i j : I) (h : i ≤ j) : (F.map (homOfLE h)).toFunctor.IsContinuous
      (Q i).toGrothendieck (Q j).toGrothendieck :=
    continuous_of_finite_pullbacks _ (Q i) (Q j)
      (finiteEquivalencePrecoverage_finite (p i) (P i)) (hcov i j h) (hpb i j h)
  have hexact (i j : I) (h : i ≤ j) :
      PreservesFiniteLimits (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
        (Q i).toGrothendieck (Q j).toGrothendieck) ∧
      PreservesFiniteColimits (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
        (Q i).toGrothendieck (Q j).toGrothendieck) := by
    obtain ⟨hpi, hei, ⟨hpilim, hpicolim⟩, ⟨heilim, heicolim⟩⟩ :=
      finiteEquivalencePrecoverage_sheaf_equivalence (p i) (P i) (e i) (hep i) (hfinite i)
    obtain ⟨hpj, hej, ⟨hpjlim, hpjcolim⟩, ⟨hejlim, hejcolim⟩⟩ :=
      finiteEquivalencePrecoverage_sheaf_equivalence (p j) (P j) (e j) (hep j) (hfinite j)
    let a : p j ≅ (e j).inv :=
      (p j).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (e j).asEquivalence.counitIso.symm (p j) ≪≫
        Functor.associator (e j).inv (e j) (p j) ≪≫
        Functor.isoWhiskerLeft (e j).inv (eqToIso (hep j)) ≪≫ (e j).inv.rightUnitor
    let eta : 𝟭 (F.obj j) ≅ p j ⋙ e j :=
      (Functor.isoWhiskerRight a (e j) ≪≫ (e j).asEquivalence.counitIso).symm
    let T := (F.map (homOfLE h)).toFunctor
    let theta : T ≅ (p i ⋙ U i j h) ⋙ e j :=
      T.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft T eta ≪≫
        (Functor.associator T (p j) (e j)).symm ≪≫
        Functor.isoWhiskerRight (SiteSystemPairs.comparison C U gamma i j h) (e j)
    exact continuous_transport_pullback_exact (Q i).toGrothendieck (Q j).toGrothendieck
      (P i).toGrothendieck (P j).toGrothendieck (p i) (U i j h) (e j) T theta
  refine ⟨F, Q, e, he, inferInstance, inferInstance, inferInstance, inferInstance,
    (fun i => finiteEquivalencePrecoverage_finite (p i) (P i)),
    (fun i => finiteEquivalencePrecoverage_inclusion (p i) (P i) (e i) (hep i) (hfinite i)),
    (fun i => finiteEquivalencePrecoverage_lift (p i) (P i) (e i) (hep i)),
    hcov, hpb, hcont, (fun i j h => ⟨(hexact i j h).1⟩),
    (fun i j h => ⟨(hexact i j h).2⟩),
    SiteSystemPairs.theta C U gamma hUid hgammaLeft,
    SiteSystemPairs.coefficients C U D v delta, ?_, ?_, ?_⟩
  · exact SiteSystemPairs.transition_coefficients C U gamma D v delta hdelta
  · exact SiteSystemPairs.inclusion_coefficients C U D v delta hUid hdeltaId
  · exact SiteSystemPairs.theta_coefficients C U gamma D v delta hUid hgammaLeft hdeltaId

end CategoryTheory
