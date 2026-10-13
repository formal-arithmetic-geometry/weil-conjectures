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
(blueprint: lem-sbc-abelian-raw-pullback-coherence-base).
-/

@[expose] public section


universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The explicit raw pullbacks form natural transformations and obey identity and composition.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit), canonical comparison maps;
Tag 03CB for inverse-image composition.
(blueprint: lem-sbc-abelian-raw-pullback-coherence-base).

Proof: For each transition and each cone leg, use the five factors in
abelianHigherDirectImageRawPullback. The middle factor is an additive derived
inverse-image functor, and composition with the other four fixed morphisms is additive.
Thus each component is a homomorphism. If r is a morphism of test objects, naturality
of upperStarComp and of mapDerivedCategoryPlusSingleFunctor moves its free-sheaf
restriction through the first two factors. Functor.map_comp moves it through the
pulled-back class. This is the naturality square, so the component homomorphisms
bundle as tau and beta. Their displayed component equations hold by construction.

For an identity transition, rewrite D.map_id and use hphiid. The unit laws for
upperStarComp cancel the source identity comparison against the coefficient identity.
The corresponding derived identity comparison is natural in the class and commutes
with its shift. Its comparison on single complexes is the underived identity
comparison, since both come from the same termwise map; hence the other single
comparisons cancel. The resulting component is the original class.

For two transitions, expand the two five-factor formulas and use map_comp.
Naturality of the single comparison moves it past the intermediate source map and
cancels the intermediate hom/inv pair. The derived composition comparison is natural
in the class and commutes with shift. Its comparison on single complexes is the
underived composition comparison (abelianPullbackSingleComposition, specialized to
these scheme maps). Apply upperStarComp associativity to the two source maps and
the structure map to combine the source factors, and apply hphicomp to combine the
coefficient factors. The remaining factors are those of the composite raw pullback.
Extensionality of homomorphisms and natural transformations proves both laws.
Neither construction uses hH, continuity, or any geometric hypothesis. In particular
empty index sets, empty test objects, zero coefficients, and p = 0 are allowed. -/
theorem abelianRawPullback_coherent_base {S : Scheme.{v}}
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
    [HasColimit H] (p : ℕ) :
    ∃ (τ : ∀ {i j : I} (_f : i ⟶ j),
        abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
          abelianHigherDirectImageRawPresheaf (D.obj (op j)).hom p (F j))
      (β : ∀ i : I, abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
        abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)),
      (∀ {i j : I} (f : i ⟶ j) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (τ f).app (op V) t = abelianHigherDirectImageRawPullback (D.map f.op).left
          (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
          (F i) (F j) (φ f) V t) ∧
      (∀ (i : I) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (β i).app (op V) t = abelianHigherDirectImageRawPullback (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
          (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i) V t) ∧
      (∀ i : I, τ (𝟙 i) = 𝟙 _) ∧
      (∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), τ (f ≫ g) = τ f ≫ τ g) := by sorry


end AlgebraicGeometry.Etale
