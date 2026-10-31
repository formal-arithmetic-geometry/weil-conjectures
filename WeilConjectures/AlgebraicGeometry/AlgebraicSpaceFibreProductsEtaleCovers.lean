/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.SheafPullbackDiagonal
import WeilConjectures.AlgebraicGeometry.FibreProductAtlasTests
import WeilConjectures.AlgebraicGeometry.PresheafPullbackEtalePointLifting
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Fibre products of algebraic spaces and pullback of étale coverings

Source: Stacks Project, Spaces, Tags 02X2 and 04T9; Topologies on Algebraic Spaces,
Tag 041F(3); Properties of Spaces, Tags 03BU and 03H4
(blueprint: lem-trf-space-fibre-products-etale-covers).

The chosen sheaf pullback is an algebraic space. Its universal property is written with
algebraic-space test objects; morphisms are the same sheaf maps in the full subcategory.

## Main statements

* `fibreProduct_isAlgebraicSpace`: closure and the universal property.
* `etaleCover_pullback`: stability of jointly surjective étale families.
* `etale_fibreProduct_isScheme`: the scheme special case.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private def explicitLimit {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) : IsLimit (sheafPullbackCone f g) := by
  apply evaluationJointlyReflectsLimits
  intro T
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_
    (Types.pullbackLimitCone (f.app T) (g.app T)).isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cone.ext (Iso.refl _) ?_
    rintro (_ | _ | _)
    all_goals rfl

private theorem chosenSquare {S : Scheme.{u}}
    {F G H : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (f : F ⟶ H) (g : G ⟶ H) :
    IsPullback (Limits.pullback.fst f g).hom (Limits.pullback.snd f g).hom f.hom g.hom :=
  (IsPullback.of_hasPullback f g).map
    (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u))

private noncomputable def explicitIso {S : Scheme.{u}}
    {F G H : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (f : F ⟶ H) (g : G ⟶ H) :
    (sheafPullbackCone f.hom g.hom).pt ≅ (Limits.pullback f g).obj :=
  (IsPullback.of_isLimit (explicitLimit f.hom g.hom)).isoIsPullback _ _ (chosenSquare f g)

private theorem explicitIso_fst {S : Scheme.{u}}
    {F G H : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (f : F ⟶ H) (g : G ⟶ H) :
    (explicitIso f g).hom ≫ (Limits.pullback.fst f g).hom =
      (sheafPullbackCone f.hom g.hom).fst :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

private theorem representableWith_iso {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {A B A' B' : (Over S)ᵒᵖ ⥤ Type u}
    (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) (f' : A' ⟶ B')
    (w : f ≫ eB.hom = eA.hom ≫ f') (hf : IsRepresentableWith P f) :
    IsRepresentableWith P f' := by
  intro T a
  obtain ⟨U, p, q, hq, hp⟩ := hf T (a ≫ eB.inv)
  refine ⟨U, p, q ≫ eA.hom, ?_, hp⟩
  exact hq.of_iso (Iso.refl _) eA (Iso.refl _) eB
    (by simp) (by simp) w (by simp)

/-- The sheaf fibre product is an algebraic space and has the categorical universal
property for algebraic-space test objects.
Source: Stacks, Spaces, Tags 04T9 and 02X2
(blueprint: lem-trf-space-fibre-products-etale-covers).
Proof: (1) pairs of matching sections glue uniquely in the two sheaves, giving the sheaf
pullback. (2) On a test scheme, the diagonal is represented by the fibre product of the two
scheme equality loci for the diagonals of `F` and `G`. (3) Choose scheme atlases `U → F`
and `V → G`; `U ×_H V` is a scheme by representability of the diagonal of `H`.
(4) Over a scheme `T → F ×_H G`, this atlas is the fibre product over `T` of the two
surjective étale scheme atlas pullbacks. Scheme surjectivity and étaleness are stable under
base change and composition, so it is a surjective étale atlas.
The scheme permanence inputs are [lem-weil-pbc-surjective-base-change],
[lem-weil-pbc-etale-scheme-base-change], [lem-trf-surjective-morphism-composition], and
[lem-weil-pbc-etale-composition-cancellation]; the sheaf condition uses
[def-weil-pbc-sites-and-cohomology] and [def-trf-algebraic-space].
(5) A map from any algebraic space `Q` into the pullback is uniquely the compatible pair
of maps into `F` and `G`, since algebraic spaces form a full subcategory of sheaves. -/
theorem fibreProduct_isAlgebraicSpace {S : Scheme.{u}} (F G H : AlgebraicSpace S)
    (f : F ⟶ H) (g : G ⟶ H) :
    IsAlgebraicSpace (Limits.pullback f.hom g.hom) ∧
      ∀ (Q : AlgebraicSpace S) (a : Q ⟶ F) (b : Q ⟶ G), a ≫ f = b ≫ g →
        ∃! l : Q.obj ⟶ Limits.pullback f.hom g.hom,
          l ≫ Limits.pullback.fst f.hom g.hom = a.hom ∧
          l ≫ Limits.pullback.snd f.hom g.hom = b.hom := by
  classical
  let P := Limits.pullback f.hom g.hom
  let e := explicitIso f.hom g.hom
  have hd := (sheafPullback_diagonal F.obj G.obj H.obj f.hom.hom g.hom.hom
    F.property.1 G.property.1).2.1
  have hd' : IsRepresentable (prod.lift (𝟙 P.obj) (𝟙 P.obj)) :=
    representableWith_iso ⊤ e (prod.mapIso e e) _ _ (by simp [P]) hd
  obtain ⟨U, a, hae, has⟩ := F.property.2
  obtain ⟨V, b, hbe, hbs⟩ := G.property.2
  obtain ⟨⟨D, d, _, _⟩, _, hwe, hws, _⟩ :=
    fibreProduct_atlas_tests F.obj G.obj H.obj f.hom.hom g.hom.hom H.property.1
      U V a b hae has hbe hbs
  let c := (chosenSquare f.hom g.hom).isoPullback
  let w := fibreProductAtlasMap f.hom.hom g.hom.hom a b
  have hce : IsEtale (d.hom ≫ w ≫ c.inv) :=
    representableWith_iso _ d.symm c.symm w _ (by simp) hwe
  have hcs : IsSurjective (d.hom ≫ w ≫ c.inv) :=
    representableWith_iso _ d.symm c.symm w _ (by simp) hws
  refine ⟨⟨hd', D, d.hom ≫ w ≫ c.inv, hce, hcs⟩, ?_⟩
  intro Q a b hab
  have h : a.hom ≫ f.hom = b.hom ≫ g.hom := congrArg (fun k ↦ k.hom) hab
  refine ⟨Limits.pullback.lift a.hom b.hom h, ⟨by simp, by simp⟩, ?_⟩
  intro l hl
  apply Limits.pullback.hom_ext <;> simp [hl.1, hl.2]

/-- Pulling back a jointly surjective representable étale family preserves both properties.
The fibre products are algebraic spaces by `fibreProduct_isAlgebraicSpace`.
Source: Stacks, Topologies on Algebraic Spaces, Tag 041F(3); Properties of Spaces,
Tags 03BU and 03H4 (blueprint: lem-trf-space-fibre-products-etale-covers).
Proof: (6) For each test scheme `T → G`, the scheme test of the first projection is
`T ×_H Hᵢ`; the assumed representable étale map represents this by a scheme étale over
`T`. (7) Represent a point of `G` by `Spec K → G`. Joint surjectivity lifts its image in
`H` to a member after a field extension. The two compatible sections give a section of
the sheaf fibre product over that extension, whose point maps to the original point.
For the empty index set the hypothesis forbids any target point, so the conclusion holds
also when both the index set and the pullback point sets are empty. -/
theorem etaleCover_pullback {S : Scheme.{u}} {I : Type w}
    (G H : AlgebraicSpace S) (Hᵢ : I → AlgebraicSpace S)
    (g : G ⟶ H) (h : ∀ i : I, Hᵢ i ⟶ H)
    (he : ∀ i : I, IsEtale (h i).hom.hom)
    (hs : IsJointlySurjective (fun i : I ↦ (h i).hom.hom)) :
    (∀ i : I, IsEtale (Limits.pullback.fst g.hom (h i).hom).hom) ∧
      IsJointlySurjective
        (fun i : I ↦ (Limits.pullback.fst g.hom (h i).hom).hom) := by
  classical
  have hpull := presheafPullback_etale_point_lifting G.obj H.obj (fun i ↦ (Hᵢ i).obj)
    g.hom.hom (fun i ↦ (h i).hom.hom) he
  constructor
  · intro i
    exact representableWith_iso _ (explicitIso g.hom (h i).hom) (Iso.refl _) _ _
      (by simpa using (explicitIso_fst g.hom (h i).hom).symm) (hpull.2.2.1 i)
  · intro K hK s x
    obtain ⟨i, L, hL, a, y, hy⟩ := (hpull.2.2.2.2 hs).2.1 K s x
    refine ⟨i, L, hL, a, (explicitIso g.hom (h i).hom).hom.app _ y, ?_⟩
    have heq := congrArg (fun k ↦ k.app
      (op (Over.mk (Spec.map (CommRingCat.ofHom a) ≫ s))))
      (explicitIso_fst g.hom (h i).hom)
    exact (ConcreteCategory.congr_hom heq y).trans hy

/-- If the base-changed target is a scheme, the étale fibre product is a scheme.
Representability by a scheme is expressed as an isomorphism with its Yoneda presheaf.
Source: Stacks, Spaces, scheme-test definition of representable étale maps, Tag 025Y;
Topologies on Algebraic Spaces, Tag 041F(3)
(blueprint: lem-trf-space-fibre-products-etale-covers).
Proof: apply the representable étale scheme-test condition to the scheme representing
`G`, using its isomorphism to obtain the map to `H`. The representing pullback square
identifies its Yoneda presheaf with the sheaf fibre product `G ×_H H'`. -/
theorem etale_fibreProduct_isScheme {S : Scheme.{u}} (G H H' : AlgebraicSpace S)
    (g : G ⟶ H) (h : H' ⟶ H) (he : IsEtale h.hom.hom)
    (T : Over S) (e : G.obj.obj ≅ yoneda.obj T) :
    ∃ U : Over S, Nonempty ((Limits.pullback g.hom h.hom).obj ≅ yoneda.obj U) := by
  classical
  have hr := presheafPullback_etale_point_lifting G.obj H.obj (fun _ : Unit ↦ H'.obj)
    g.hom.hom (fun _ ↦ h.hom.hom) (fun _ ↦ he)
  obtain ⟨U, ⟨d⟩⟩ := hr.2.2.2.1 () T e
  exact ⟨U, ⟨(explicitIso g.hom h.hom).symm ≪≫ d⟩⟩

end AlgebraicGeometry.AlgebraicSpace
