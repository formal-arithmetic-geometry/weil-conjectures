/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.AlgebraicGeometry.AbelianPullbackSingleComposition

/-! # Coherence of varying-coefficient raw pullbacks

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-raw-pullback-coherence-extend).
-/

@[expose] public section


universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Natural transformations with the prescribed raw components obey the colimit cocone law.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit), canonical comparison maps;
Tag 03CB for inverse-image composition.
(blueprint: lem-sbc-abelian-raw-pullback-coherence-extend).

Proof: Fix f : i → j and a raw class z at a test object V. By hτ and hβ, the
component of tau f followed by beta j is the iterated explicit raw pullback along
D.map f.op and c.π.app (op j). Expand its two five-factor formulas. Functor.map_comp
and naturality of the single comparison cancel the intermediate single hom/inv
pair. The derived composition comparison is natural in z, commutes with the shift,
and on single complexes agrees with the underived comparison, as in
abelianPullbackSingleComposition. Associativity of upperStarComp combines the source
factors. Cone naturality c.w f.op identifies the composite scheme map with
c.π.app (op i); proof irrelevance identifies the resulting witnesses of Over.w.

Write C for the component of upperStarComp in hH, and P for pullback along the
j-th cone leg. The coefficient of this composite is
C ≫ P.map (φ f) ≫ (eH j).inv ≫ colimit.ι H j.
From hH and colimit.w H f this is (eH i).inv ≫ colimit.ι H i: precompose
H.map f ≫ colimit.ι H j = colimit.ι H i with (eH i).inv, substitute hH,
and cancel (eH i).inv ≫ (eH i).hom. The composite formula therefore equals
the i-th cone-leg raw pullback, which hβ identifies with beta i. Extensionality
in z and V proves tau f ≫ beta j = beta i. No identity/composition laws of tau
are assumed, and hφid and hφcomp are not used. The proof uses only colimit
naturality, not a limit or a continuity theorem, and also covers zero coefficients,
empty test objects, and degree zero. For an empty index set the conclusion is vacuous. -/
theorem abelianRawPullback_coherent_extend {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (τ : ∀ {i j : I} (_f : i ⟶ j),
        abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
          abelianHigherDirectImageRawPresheaf (D.obj (op j)).hom p (F j))
    (β : ∀ i : I, abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
        abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H))
    (hτ : ∀ {i j : I} (f : i ⟶ j) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (τ f).app (op V) t = abelianHigherDirectImageRawPullback (D.map f.op).left
          (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
          (F i) (F j) (φ f) V t)
    (hβ : ∀ (i : I) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (β i).app (op V) t = abelianHigherDirectImageRawPullback (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
          (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i) V t) :
    ∀ {i j : I} (f : i ⟶ j), τ f ≫ β j = β i := by sorry

end AlgebraicGeometry.Etale
