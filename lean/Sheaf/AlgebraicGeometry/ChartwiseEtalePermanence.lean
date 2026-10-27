/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection
import Sheaf.AlgebraicGeometry.PresheafFieldLiftFamilyCalculus

/-!
# Chartwise étale permanence for algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03FR, 03FT, 03FU and 03FV;
Topologies on Algebraic Spaces, Tag 041F(1)--(3)
(blueprint: lem-trf-space-chartwise-etale-permanence).

We reuse `IsChartwiseEtale` from the enlarged-site module. Covering families are written
as the conjunction of chartwise étaleness and `IsJointlySurjective`, so no representability
condition is imposed on a covering map. All pullbacks are the actual sheaf pullbacks
bundled by `enlargedFibreProduct`.
-/

@[expose] public section

set_option autoImplicit false

universe u w v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Representability with any scheme-test property is preserved by presheaf base change.
Source: Stacks, Spaces, relative representable properties preceding Tag 025Y
(blueprint: lem-trf-space-chartwise-etale-permanence).

Proof: test the original map on the composite of a scheme test with the base-change
map. Lift its representing square to the given pullback; pullback cancellation gives
the new representing square, with the identical scheme projection and property. -/
theorem representableWith_baseChange {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {A B C D : (Over S)ᵒᵖ ⥤ Type u}
    {q : D ⟶ A} {p : D ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (sq : IsPullback q p f g) (hf : IsRepresentableWith P f) :
    IsRepresentableWith P p := by
  intro T a
  obtain ⟨U, r, b, hb, hr⟩ := hf T (a ≫ g)
  let l := sq.lift b (yoneda.map r ≫ a) (by simpa only [Category.assoc] using hb.w)
  refine ⟨U, r, l, ?_, hr⟩
  apply IsPullback.of_right (h₁₂ := q) (h₂₂ := g) _ (sq.lift_snd _ _ _) sq
  simpa only [l, IsPullback.lift_fst] using hb

private theorem space_pullback_square {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback (Limits.pullback.fst f.hom g.hom).hom
      (Limits.pullback.snd f.hom g.hom).hom f.hom.hom g.hom.hom := by
  exact (sheafToPresheaf _ _).map_isPullback (IsPullback.of_hasPullback f.hom g.hom)

/-- Chartwise étaleness agrees with representable étaleness for scheme sources, contains
identities, is closed under composition and arbitrary base change, and satisfies cancellation
between two objects étale over a common base. Étale covering families (the two displayed
conjuncts) contain singleton isomorphisms and are closed under composition and base change.
Source: Stacks, Tags 03FR, 03FT, 03FU, 03FV and 041F(1)--(3)
(blueprint: lem-trf-space-chartwise-etale-permanence).

Proof, following the ten steps of the node:
1. Every map from a scheme to an algebraic space is representable: its scheme tests are
   pullbacks of the representable diagonal along the product of the two test schemes
   [def-trf-algebraic-space, def-pc-fibre-product].
2. For representable étale maps, successive scheme tests give composition and base change.
   Scheme étaleness is stable under both operations; isomorphisms are open immersions,
   hence étale. Surjectivity is likewise preserved [lem-weil-pbc-etale-composition-cancellation,
   def-weil-open-immersion, lem-trf-surjective-morphism-composition,
   lem-weil-pbc-surjective-base-change, lem-weil-pbc-etale-scheme-base-change].
3. For a scheme source, test chartwise étaleness on its identity. Conversely compose a
   representable étale map with each scheme chart, using step 2.
4. If a scheme-source map becomes representable étale after a surjective étale scheme
   cover, test over any scheme. Step 1 represents both pullbacks by schemes; the projection
   between them is surjective étale. Apply [lem-trf-etale-descent-through-source-cover].
5. Identity and composition follow directly by applying the chartwise condition to a
   scheme chart, once or twice. Isomorphisms follow from step 2.
6. For base change, pull back an atlas of the original source. For any scheme chart of the
   fibre product, pull back this atlas again. The result is a scheme surjective étale over
   the chart and representable étale over the new target. Descend by step 4. Reassociation
   identifies the two pullbacks section by section; closure is
   [lem-trf-space-fibre-products-etale-covers].
7. For schemes étale over a common algebraic space, the graph into their fibre product is
   a section of an étale projection. Scheme cancellation makes this section étale; scheme
   composition makes the original map étale [lem-weil-pbc-etale-composition-cancellation].
8. To cancel for arbitrary spaces, pull back a scheme chart of the source along an atlas
   of the target. Step 7 makes its map to that atlas étale, step 2 gives representable
   étaleness of the composite, and step 4 descends it to the original source chart.
9. An isomorphism lifts field-valued sections by its inverse. For composite coverings,
   lift a section after a field extension to the first family, then after a further
   extension to the second. The composite embedding supplies the required lift
   [def-trf-algebraic-space-jointly-surjective-family].
10. After arbitrary base change, step 6 gives chartwise étaleness. Lift the image of a
   field-valued section through the original cover after extension. The compatible pair
   gives a section of the actual sheaf fibre product and thus joint surjectivity. Empty
   covering families cause no exception: their hypotheses exclude target field sections. -/
theorem chartwise_etale_permanence {S : Scheme.{u}} :
    (∀ (T : Over S) (Y : AlgebraicSpace S) (f : schemeSpace T ⟶ Y),
      IsChartwiseEtale f ↔ IsEtale f.hom.hom) ∧
    (∀ X : AlgebraicSpace S, IsChartwiseEtale (𝟙 X)) ∧
    (∀ (X Y Z : AlgebraicSpace S) (f : X ⟶ Y) (g : Y ⟶ Z),
      IsChartwiseEtale f → IsChartwiseEtale g → IsChartwiseEtale (f ≫ g)) ∧
    (∀ (X Y Z : AlgebraicSpace S) (f : X ⟶ Z) (g : Y ⟶ Z),
      IsChartwiseEtale f → IsChartwiseEtale (enlargedFibreProductFst g f)) ∧
    (∀ (X Y Z : AlgebraicSpace S) (g : X ⟶ Z) (h : Y ⟶ Z) (f : X ⟶ Y),
      IsChartwiseEtale g → IsChartwiseEtale h → f ≫ h = g → IsChartwiseEtale f) ∧
    (∀ (X Y : AlgebraicSpace S) (e : X ≅ Y),
      IsChartwiseEtale e.hom ∧
        IsJointlySurjective (fun _ : Unit ↦ e.hom.hom.hom)) ∧
    (∀ (I : Type w) (J : I → Type v) (X : AlgebraicSpace S)
      (Xᵢ : I → AlgebraicSpace S) (Xᵢⱼ : ∀ i : I, J i → AlgebraicSpace S)
      (f : ∀ i : I, Xᵢ i ⟶ X) (g : ∀ (i : I) (j : J i), Xᵢⱼ i j ⟶ Xᵢ i),
      ((∀ i : I, IsChartwiseEtale (f i)) ∧
        IsJointlySurjective (fun i : I ↦ (f i).hom.hom)) →
      (∀ i : I, (∀ j : J i, IsChartwiseEtale (g i j)) ∧
        IsJointlySurjective (fun j : J i ↦ (g i j).hom.hom)) →
      (∀ a : Sigma J, IsChartwiseEtale (g a.1 a.2 ≫ f a.1)) ∧
        IsJointlySurjective (fun a : Sigma J ↦ (g a.1 a.2 ≫ f a.1).hom.hom)) ∧
    (∀ (I : Type w) (X X' : AlgebraicSpace S) (Xᵢ : I → AlgebraicSpace S)
      (f : ∀ i : I, Xᵢ i ⟶ X) (g : X' ⟶ X),
      ((∀ i : I, IsChartwiseEtale (f i)) ∧
        IsJointlySurjective (fun i : I ↦ (f i).hom.hom)) →
      (∀ i : I, IsChartwiseEtale (enlargedFibreProductFst g (f i))) ∧
        IsJointlySurjective
          (fun i : I ↦ (enlargedFibreProductFst g (f i)).hom.hom)) := by
  have tests := representable_etale_scheme_tests (S := S)
  have descent := etale_source_atlas_detection (S := S)
  have rep_comp := tests.2.2.1
  have rep_iso := tests.2.2.2.2.1
  have scheme_test := tests.2.2.2.2.2.2.2.1
  have comparison := tests.2.2.2.2.2.2.2.2.2
  have chart_comp : ∀ {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      IsChartwiseEtale f → IsChartwiseEtale g → IsChartwiseEtale (f ≫ g) := by
    intro X Y Z f g hf hg T a ha
    exact hg T (a ≫ f.hom.hom) (hf T a ha)
  have rep_chart : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      IsEtale f.hom.hom → IsChartwiseEtale f := by
    intro X Y f hf T a ha
    exact rep_comp (schemeSpace T) X Y (ObjectProperty.homMk ⟨a⟩) f ha hf
  have chart_base : ∀ (X Y Z : AlgebraicSpace S) (f : X ⟶ Z) (g : Y ⟶ Z),
      IsChartwiseEtale f → IsChartwiseEtale (enlargedFibreProductFst g f) := by
    intro X Y Z f g hf
    obtain ⟨U, a, ha, hs⟩ := descent.2.2.2 X
    let A : schemeSpace U ⟶ X := ObjectProperty.homMk ⟨a⟩
    let P := enlargedFibreProduct g f
    let q : P ⟶ X := ObjectProperty.homMk (Limits.pullback.snd g.hom f.hom)
    let R := enlargedFibreProduct q A
    let p : R ⟶ P := enlargedFibreProductFst q A
    have sq := (space_pullback_square q A).flip
    have he : IsEtale p.hom.hom := representableWith_baseChange _ sq ha
    have hp : IsSurjective p.hom.hom := representableWith_baseChange _ sq hs
    have outer := sq.paste_vert (space_pullback_square g f).flip
    have hc : IsEtale (p.hom.hom ≫ (enlargedFibreProductFst g f).hom.hom) :=
      representableWith_baseChange _ outer (hf U a ha)
    exact descent.2.1 P Y R (enlargedFibreProductFst g f) p he hp hc
  have chart_cancel : ∀ (X Y Z : AlgebraicSpace S)
      (g : X ⟶ Z) (h : Y ⟶ Z) (f : X ⟶ Y),
      IsChartwiseEtale g → IsChartwiseEtale h → f ≫ h = g → IsChartwiseEtale f := by
    intro X Y Z g h f hg hh eq U a ha
    obtain ⟨V, b, hb, hs⟩ := descent.2.2.2 Y
    obtain ⟨W, p, q, sq, hp⟩ := hs U (a ≫ f.hom.hom)
    have hpe : IsEtale (yoneda.map p) := representableWith_baseChange _ sq hb
    have pe : Etale p.left := (scheme_test _ _ p).mp hpe
    let r : W ⟶ V := Yoneda.fullyFaithful.preimage q
    have hr : yoneda.map r = q := Yoneda.fullyFaithful.map_preimage q
    have hga : IsEtale (yoneda.map p ≫ (a ≫ g.hom.hom)) :=
      rep_comp (schemeSpace W) (schemeSpace U) Z
        (ObjectProperty.homMk ⟨yoneda.map p⟩) (ObjectProperty.homMk ⟨a ≫ g.hom.hom⟩)
        hpe (hg U a ha)
    have heq : yoneda.map r ≫ (b ≫ h.hom.hom) =
        yoneda.map p ≫ (a ≫ g.hom.hom) := by
      rw [hr, ← Category.assoc, sq.w, Category.assoc, Category.assoc]
      have e : f.hom.hom ≫ h.hom.hom = g.hom.hom :=
        congrArg (fun k ↦ k.hom.hom) eq
      rw [e]
    have re := comparison Z W V (yoneda.map p ≫ (a ≫ g.hom.hom))
      (b ≫ h.hom.hom) r hga (hh V b hb) heq
    have hre := (scheme_test W V r).mpr re
    have hqb : IsEtale (q ≫ b) := by
      rw [← hr]
      exact rep_comp (schemeSpace W) (schemeSpace V) Y
        (ObjectProperty.homMk ⟨yoneda.map r⟩) (ObjectProperty.homMk ⟨b⟩) hre hb
    exact descent.1 Y U W (a ≫ f.hom.hom) p pe hp (sq.w ▸ hqb)
  refine ⟨?_, ?_, ?_, chart_base, chart_cancel, ?_, ?_, ?_⟩
  · intro T Y f
    constructor
    · intro hf
      have hi := (rep_iso (schemeSpace T) (schemeSpace T) (𝟙 _)
        (by infer_instance)).1
      simpa using hf T (𝟙 _) hi
    · exact rep_chart f
  · intro X T a ha
    simpa using ha
  · intro X Y Z f g hf hg
    exact chart_comp f g hf hg
  · intro X Y e
    refine ⟨rep_chart e.hom (rep_iso X Y e.hom (by infer_instance)).1, ?_⟩
    exact (presheaf_field_lift_family_calculus.{u, w, v} S).1 _ _
      ((ObjectProperty.ι _ ⋙ sheafToPresheaf _ _).mapIso e)
  · intro I J X Xi Xij f g hf hg
    refine ⟨fun a ↦ chart_comp _ _ ((hg a.1).1 a.2) (hf.1 a.1), ?_⟩
    exact (presheaf_field_lift_family_calculus S).2.1 I J X.obj.obj
      (fun i ↦ (Xi i).obj.obj) (fun i j ↦ (Xij i j).obj.obj)
      (fun i ↦ (f i).hom.hom) (fun i j ↦ (g i j).hom.hom) hf.2 (fun i ↦ (hg i).2)
  · intro I X X' Xi f g hf
    refine ⟨fun i ↦ chart_base _ _ _ _ _ (hf.1 i), ?_⟩
    intro K _ s x
    obtain ⟨i, L, hL, e, y, hy⟩ := hf.2 K s (g.hom.hom.app _ x)
    let t : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ Over.mk s :=
      Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl
    have sq := (space_pullback_square g (f i)).app
      (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s)))
    have heq : g.hom.hom.app _ (X'.obj.obj.map t.op x) = (f i).hom.hom.app _ y := by
      rw [hy]
      exact ConcreteCategory.congr_hom (g.hom.hom.naturality t.op) x
    obtain ⟨z, hz, _⟩ := Types.exists_of_isPullback sq _ _ heq
    exact ⟨i, L, hL, e, z, hz⟩

end AlgebraicGeometry.AlgebraicSpace
