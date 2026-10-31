/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Sites.GrothendieckTopos
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.AlgebraicGeometry.PresheafFieldLiftFamilyCalculus
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Limits.Yoneda
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection

/-!
# Enlarged étale ringed sites of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03G0, 03G1, 03H7, 03G2, 03G8,
03LP, 04LY and 04LZ (blueprint: lem-trf-space-enlarged-etale-ringed-site-model).

The enlarged site uses chartwise étaleness, without requiring representability.
Restriction is actual precomposition. All comparisons below retain this normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Chartwise étaleness used in Stacks, Tags 03FR and 03G0:
every representable étale scheme chart remains representable étale after composition.
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def IsChartwiseEtale {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ (T : Over S) (a : yoneda.obj T ⟶ X.obj.obj),
    IsEtale a → IsEtale (a ≫ f.hom.hom)

/-- The enlarged site has étale algebraic spaces over `X` and all maps over `X`.
Source: Stacks, Tag 03G0 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
abbrev EnlargedEtaleSite (X : AlgebraicSpace S) :=
  ObjectProperty.FullSubcategory (fun T : Over X ↦ IsChartwiseEtale T.hom)

/-- Coverings are chartwise étale families jointly surjective on point classes.
Source: Stacks, Tag 03G0 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedEtalePrecoverage (X : AlgebraicSpace S) : Precoverage X.EnlargedEtaleSite where
  coverings T := {R |
    (∀ (U : X.EnlargedEtaleSite) (f : U ⟶ T), R f → IsChartwiseEtale f.hom.left) ∧
    IsJointlySurjective (fun a : R.uncurry ↦ a.1.2.hom.left.hom.hom)}

/-- The topology of the enlarged étale site.
Source: Stacks, Tag 03G0 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
abbrev enlargedEtaleTopology (X : AlgebraicSpace S) := X.enlargedEtalePrecoverage.toGrothendieck

/-- Representable scheme sheaves are algebraic spaces.
Source: Stacks, Tag 025Y, used in Tag 03G1
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: Yoneda sends scheme fibre products to presheaf pullbacks, so every map
between representables is relatively representable. The diagonal criterion gives its
representable diagonal. The identity of the scheme is its surjective étale atlas.
The fppf sheaf condition is subcanonicity. -/
theorem schemeSheaf_isAlgebraicSpace (T : Over S) :
    IsAlgebraicSpace ((Scheme.fppfTopology.over S).yoneda.obj T) := by
  constructor
  · have h : yoneda.relativelyRepresentable (Limits.diag (yoneda.obj T)) :=
      Functor.relativelyRepresentable.diag_of_map_from_obj (fun {U} a ↦ by
        obtain ⟨g, rfl⟩ := yoneda.map_surjective a
        exact Functor.relativelyRepresentable.map yoneda g)
    intro U a
    obtain ⟨V, p, q, hq⟩ := h a
    exact ⟨V, p, q, hq, trivial⟩
  · refine ⟨T, 𝟙 _, ?_, ?_⟩
    · intro U a
      refine ⟨U, 𝟙 U, a, IsPullback.of_vert_isIso ⟨by simp⟩, ?_⟩
      change Etale (𝟙 U.left)
      infer_instance
    · intro U a
      refine ⟨U, 𝟙 U, a, IsPullback.of_vert_isIso ⟨by simp⟩, ?_⟩
      change Surjective (𝟙 U.left)
      infer_instance

/-- A scheme regarded as an algebraic space, using its actual representable sheaf.
Source: Stacks, Tags 025Y and 03G1
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def schemeSpace (T : Over S) : AlgebraicSpace S :=
  ⟨(Scheme.fppfTopology.over S).yoneda.obj T, schemeSheaf_isAlgebraicSpace T⟩

/-- A representable étale scheme object is chartwise étale.
Source: Stacks, Tags 03FR and 03G1
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: compose its representable étale map with any representable étale scheme chart,
using `isEtale_comp`. -/
theorem schemeObject_chartwise (X : AlgebraicSpace S) (T : X.EtaleSite) :
    IsChartwiseEtale (X := schemeSpace T.obj.left)
      (ObjectProperty.homMk ⟨T.obj.hom⟩ : schemeSpace T.obj.left ⟶ X) := by
  intro U a ha
  exact isEtale_comp a T.obj.hom ha T.property

/-- The inclusion of scheme objects, retaining the underlying Yoneda maps.
Source: Stacks, Tag 03G1 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedSchemeInclusion (X : AlgebraicSpace S) : X.EtaleSite ⥤ X.EnlargedEtaleSite where
  obj T := ⟨Over.mk (ObjectProperty.homMk ⟨T.obj.hom⟩ : schemeSpace T.obj.left ⟶ X),
    schemeObject_chartwise X T⟩
  map f := ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk ⟨yoneda.map f.hom.left⟩)
      (by apply ObjectProperty.hom_ext; apply Sheaf.hom_ext; exact f.hom.w))
  map_id T := by
    apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext; apply Sheaf.hom_ext; simp [schemeSpace]
  map_comp f g := by
    apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext; apply Sheaf.hom_ext; simp

/-- Composition of chartwise étale morphisms, for the localization functor.
Source: Stacks, Tags 03FT and 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: each representable étale scheme chart remains representable étale after
composing with the first map, and then with the second, by the two hypotheses. -/
theorem enlargedEtale_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsChartwiseEtale f) (hg : IsChartwiseEtale g) :
    IsChartwiseEtale (f ≫ g) := by
  intro T a ha
  exact hg T (a ≫ f.hom.hom) (hf T a ha)

/-- The sheaf pullback, bundled as an algebraic space.
Source: Stacks, Tags 04T9 and 03G2
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedFibreProduct {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    AlgebraicSpace S :=
  ⟨Limits.pullback f.hom g.hom, (fibreProduct_isAlgebraicSpace X Y Z f g).1⟩

/-- The first projection of the actual sheaf fibre product.
Source: Stacks, Tag 03G2 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedFibreProductFst {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    enlargedFibreProduct f g ⟶ X :=
  ObjectProperty.homMk (Limits.pullback.fst f.hom g.hom)

/-- Base change of an enlarged object is again an enlarged object.
Source: Stacks, Tags 03FU and 03G2
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: pull back a scheme chart of the fibre product and then a scheme chart of the
result. Étaleness follows on these scheme tests from scheme base change and the
chartwise definition; it descends along the surjective étale chart. -/
theorem enlargedFibreProduct_chartwise {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Y.EnlargedEtaleSite) :
    IsChartwiseEtale (enlargedFibreProductFst f T.obj.hom) := by
  have bc (P : MorphismProperty (Over S)) {A B C D : (Over S)ᵒᵖ ⥤ Type u}
      {q : D ⟶ A} {p : D ⟶ B} {a : A ⟶ C} {b : B ⟶ C}
      (sq : IsPullback q p a b) (ha : IsRepresentableWith P a) :
      IsRepresentableWith P p := by
    intro U c
    obtain ⟨V, r, d, hd, hr⟩ := ha U (c ≫ b)
    let l := sq.lift d (yoneda.map r ≫ c) (by simpa only [Category.assoc] using hd.w)
    refine ⟨V, r, l, ?_, hr⟩
    apply IsPullback.of_right (h₁₂ := q) (h₂₂ := b) _ (sq.lift_snd _ _ _) sq
    simpa only [l, IsPullback.lift_fst] using hd
  have square {A B C : AlgebraicSpace S} (a : A ⟶ C) (b : B ⟶ C) :
      IsPullback (Limits.pullback.fst a.hom b.hom).hom
        (Limits.pullback.snd a.hom b.hom).hom a.hom.hom b.hom.hom :=
    (sheafToPresheaf _ _).map_isPullback (IsPullback.of_hasPullback a.hom b.hom)
  have descent := etale_source_atlas_detection (S := S)
  obtain ⟨U, a, ha, hs⟩ := descent.2.2.2 T.obj.left
  let A : schemeSpace U ⟶ T.obj.left := ObjectProperty.homMk ⟨a⟩
  let P := enlargedFibreProduct f T.obj.hom
  let q : P ⟶ T.obj.left := ObjectProperty.homMk (Limits.pullback.snd f.hom T.obj.hom.hom)
  let p : enlargedFibreProduct q A ⟶ P := enlargedFibreProductFst q A
  have sq := (square q A).flip
  have he : IsEtale p.hom.hom := bc _ sq ha
  have hp : IsSurjective p.hom.hom := bc _ sq hs
  have outer := sq.paste_vert (square f T.obj.hom).flip
  have hc : IsEtale (p.hom.hom ≫ (enlargedFibreProductFst f T.obj.hom).hom.hom) :=
    bc _ outer (T.property U a ha)
  exact descent.2.1 P X (enlargedFibreProduct q A)
    (enlargedFibreProductFst f T.obj.hom) p he hp hc

private theorem enlarged_representable_baseChange
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

private theorem enlarged_chart_cancel : ∀ (X Y Z : AlgebraicSpace S)
      (g : X ⟶ Z) (h : Y ⟶ Z) (f : X ⟶ Y),
      IsChartwiseEtale g → IsChartwiseEtale h → f ≫ h = g → IsChartwiseEtale f := by
  have tests := representable_etale_scheme_tests (S := S)
  have descent := etale_source_atlas_detection (S := S)
  have rep_comp := tests.2.2.1
  have scheme_test := tests.2.2.2.2.2.2.2.1
  have comparison := tests.2.2.2.2.2.2.2.2.2
  intro X Y Z g h f hg hh eq U a ha
  obtain ⟨V, b, hb, hs⟩ := descent.2.2.2 Y
  obtain ⟨W, p, q, sq, hp⟩ := hs U (a ≫ f.hom.hom)
  have hpe : IsEtale (yoneda.map p) := enlarged_representable_baseChange _ sq hb
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

-- Forget to the actual presheaves, retaining their pullback universal properties.
private def densityForget {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.EnlargedEtaleSite ⥤ (Over S)ᵒᵖ ⥤ Type u :=
  ObjectProperty.ι _ ⋙ Over.forget X ⋙ ObjectProperty.ι _ ⋙ sheafToPresheaf _ _

private instance densityForget_faithful {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (densityForget X).Faithful := by
  unfold densityForget
  infer_instance

private instance densityForget_reflects {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ReflectsLimitsOfShape WalkingCospan (densityForget X) := by
  unfold densityForget
  infer_instance

private theorem density_chartwise {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T U : X.EnlargedEtaleSite} (f : T ⟶ U) : IsChartwiseEtale f.hom.left :=
  enlarged_chart_cancel _ _ _ T.obj.hom U.obj.hom
    f.hom.left T.property U.property f.hom.w

private theorem density_cover_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type v} (U : X.EnlargedEtaleSite) (T : I → X.EnlargedEtaleSite)
    (f : ∀ i, T i ⟶ U) :
    Presieve.ofArrows T f ∈ X.enlargedEtalePrecoverage U ↔
      IsJointlySurjective (fun i ↦ (f i).hom.left.hom.hom) := by
  constructor
  · intro h K _ s x
    obtain ⟨⟨⟨V, a⟩, ha⟩, L, hL, e, y, hy⟩ := h.2 K s x
    obtain ⟨i⟩ := ha
    exact ⟨i, L, hL, e, y, hy⟩
  · intro h
    refine ⟨fun _ a _ ↦ density_chartwise a, ?_⟩
    intro K _ s x
    obtain ⟨i, L, hL, e, y, hy⟩ := h K s x
    exact ⟨⟨⟨T i, f i⟩, ⟨i⟩⟩, L, hL, e, y, hy⟩

private theorem density_terminal {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ T : X.EnlargedEtaleSite, T.obj = Over.mk (𝟙 X) ∧ Nonempty (IsTerminal T) := by
  let T : X.EnlargedEtaleSite := ⟨Over.mk (𝟙 X), (by intro U a ha; simpa using ha)⟩
  refine ⟨T, rfl, ⟨IsTerminal.ofUniqueHom
    (fun U ↦ ObjectProperty.homMk (Over.homMk U.obj.hom (by simp [T]))) ?_⟩⟩
  intro U f
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  simpa [T] using f.hom.w

private theorem density_pullbacks {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T U V : X.EnlargedEtaleSite) (f : T ⟶ V) (g : U ⟶ V) :
    ∃ (P : X.EnlargedEtaleSite) (p : P ⟶ T) (q : P ⟶ U),
      IsPullback p q f g ∧
      IsPullback p.hom.left.hom q.hom.left.hom f.hom.left.hom g.hom.left.hom := by
  have hf : IsChartwiseEtale f.hom.left :=
    enlarged_chart_cancel _ _ _ T.obj.hom V.obj.hom f.hom.left
      T.property V.property f.hom.w
  let A := enlargedFibreProduct g.hom.left f.hom.left
  let a : A ⟶ U.obj.left := enlargedFibreProductFst g.hom.left f.hom.left
  let b : A ⟶ T.obj.left := ObjectProperty.homMk
    (Limits.pullback.snd g.hom.left.hom f.hom.left.hom)
  have ha : IsChartwiseEtale a :=
    enlargedFibreProduct_chartwise g.hom.left ⟨Over.mk f.hom.left, hf⟩
  let P : X.EnlargedEtaleSite := ⟨Over.mk (a ≫ U.obj.hom),
    enlargedEtale_comp a U.obj.hom ha U.property⟩
  have hab : b ≫ f.hom.left = a ≫ g.hom.left := by
    apply ObjectProperty.hom_ext
    exact (Limits.pullback.condition (f := g.hom.left.hom) (g := f.hom.left.hom)).symm
  let p : P ⟶ T := ObjectProperty.homMk (Over.homMk b (by
    change b ≫ T.obj.hom = a ≫ U.obj.hom
    rw [← f.hom.w, ← g.hom.w, ← Category.assoc, ← Category.assoc, hab]))
  let q : P ⟶ U := ObjectProperty.homMk (Over.homMk a rfl)
  have sq : IsPullback p.hom.left.hom q.hom.left.hom
      f.hom.left.hom g.hom.left.hom :=
    (IsPullback.of_hasPullback g.hom.left.hom f.hom.left.hom).flip
  refine ⟨P, p, q, ?_, ?_⟩
  · apply IsPullback.of_map_of_faithful (densityForget X)
    exact (sheafToPresheaf _ _).map_isPullback sq
  · exact sq

private instance densityForget_preserves {S : Scheme.{u}} (X : AlgebraicSpace S) :
    PreservesLimitsOfShape WalkingCospan (densityForget X) := by
  apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro T U V f g _
  obtain ⟨P, p, q, h, hs⟩ := density_pullbacks X T U V f g
  exact ⟨P, p, q, h, (sheafToPresheaf _ _).map_isPullback hs⟩

private theorem density_cover_pullback {S : Scheme.{u}} (X : AlgebraicSpace S)
    {I : Type v} {U V : X.EnlargedEtaleSite} {T P : I → X.EnlargedEtaleSite}
    (f : ∀ i, T i ⟶ U) (g : V ⟶ U) (p : ∀ i, P i ⟶ V) (q : ∀ i, P i ⟶ T i)
    (h : ∀ i, IsPullback (p i) (q i) g (f i))
    (hf : Presieve.ofArrows T f ∈ X.enlargedEtalePrecoverage U) :
    Presieve.ofArrows P p ∈ X.enlargedEtalePrecoverage V := by
  apply (density_cover_iff V P p).2
  intro K _ s x
  obtain ⟨i, L, hL, e, y, hy⟩ := (density_cover_iff U T f).1 hf K s
    (g.hom.left.hom.hom.app _ x)
  let r : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ Over.mk s :=
    Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl
  have heq : g.hom.left.hom.hom.app _ (V.obj.left.obj.obj.map r.op x) =
      (f i).hom.left.hom.hom.app _ y := by
    rw [hy]
    exact ConcreteCategory.congr_hom (g.hom.left.hom.hom.naturality r.op) x
  have sq := ((h i).map (densityForget X)).app
    (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s)))
  obtain ⟨z, hz, _⟩ := Types.exists_of_isPullback sq _ _ heq
  exact ⟨i, L, hL, e, z, hz⟩

private theorem density_site {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.enlargedEtalePrecoverage.IsSiteForCoverings := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · intro U V f hf
    have h := (presheaf_field_lift_family_calculus.{u, 0, 0} S).1 _ _
      ((densityForget X).mapIso (asIso f))
    simpa only [Presieve.ofArrows_of_unique] using
      (density_cover_iff V (fun _ : Unit ↦ U) (fun _ ↦ f)).2 h
  · intro U R T hR hT
    refine ⟨fun _ a _ ↦ density_chartwise a, ?_⟩
    let J (a : R.uncurry) : Type (u + 1) := (T a.1.2 a.2).uncurry
    have h := (presheaf_field_lift_family_calculus S).2.1 R.uncurry J
      U.obj.left.obj.obj (fun a ↦ a.1.1.obj.left.obj.obj)
      (fun a b ↦ b.1.1.obj.left.obj.obj)
      (fun a ↦ a.1.2.hom.left.hom.hom)
      (fun a b ↦ b.1.2.hom.left.hom.hom) hR.2
      (fun a ↦ (hT a.1.1 a.1.2 a.2).2)
    intro K _ s x
    obtain ⟨⟨a, b⟩, L, hL, e, y, hy⟩ := h K s x
    refine ⟨⟨⟨b.1.1, b.1.2 ≫ a.1.2⟩, ?_⟩, L, hL, e, y, hy⟩
    exact ⟨a.1.1, b.1.2, a.1.2, a.2, b.2, rfl⟩
  · intro I U T f hf V g
    choose P p q hp hq using fun i ↦ density_pullbacks X V (T i) U g (f i)
    exact ⟨P, p, q, hp, density_cover_pullback X f g p q hp hf⟩

private def density_fullyFaithful {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (enlargedSchemeInclusion X).FullyFaithful where
  preimage {U V} f := ObjectProperty.homMk (CostructuredArrow.homMk
    (Yoneda.fullyFaithful.preimage f.hom.left.hom.hom) (by
      rw [Yoneda.fullyFaithful.map_preimage]
      exact congrArg (fun k ↦ k.hom.hom) f.hom.w))
  map_preimage f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Sheaf.hom_ext
    exact Yoneda.fullyFaithful.map_preimage _
  preimage_map f := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact Yoneda.fullyFaithful.preimage_map _

-- A point over a field supplies an extension and a map from its residue-field spectrum.
private theorem density_field_point {K : Type u} [Field K]
    (T : Scheme.{u}) (f : T ⟶ Spec (CommRingCat.of K)) (t : T) :
    ∃ (L : Type u) (_ : Field L) (e : K →+* L) (a : Spec (CommRingCat.of L) ⟶ T),
      a ≫ f = Spec.map (CommRingCat.ofHom e) := by
  obtain ⟨e, he⟩ := Spec.map_surjective (T.fromSpecResidueField t ≫ f)
  exact ⟨T.residueField t, inferInstance, e.hom, T.fromSpecResidueField t, he.symm⟩

private theorem density_scheme_points {S : Scheme.{u}} {I : Type v}
    (T : Over S) (U : I → Over S) (f : ∀ i, U i ⟶ T) :
    IsJointlySurjective (fun i ↦ yoneda.map (f i)) ↔
      ∀ x : T.left, ∃ (i : I) (y : (U i).left), (f i).left y = x := by
  constructor
  · intro h x
    let s := T.left.fromSpecResidueField x ≫ T.hom
    let a : Over.mk s ⟶ T := Over.homMk (T.left.fromSpecResidueField x) rfl
    obtain ⟨i, L, hL, e, y, hy⟩ := h (T.left.residueField x) s a
    refine ⟨i, y.left (default : Spec (CommRingCat.of L)), ?_⟩
    have he := congrArg (fun k ↦ k.left (default : Spec (CommRingCat.of L))) hy
    change (f i).left (y.left (default : Spec (CommRingCat.of L))) =
      T.left.fromSpecResidueField x
      ((Spec.map (CommRingCat.ofHom e)) default) at he
    simpa only [Scheme.fromSpecResidueField_apply] using he
  · intro h K _ s x
    obtain ⟨i, y, hy⟩ := h (x.left (default : Spec (CommRingCat.of K)))
    let P := Limits.pullback (f i).left x.left
    obtain ⟨t, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (f i).left) (g := x.left) y
      (default : Spec (CommRingCat.of K)) hy
    obtain ⟨L, hL, e, b, hb⟩ := density_field_point P
      (Limits.pullback.snd (f i).left x.left) t
    let a : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ U i :=
      Over.homMk (b ≫ Limits.pullback.fst (f i).left x.left) (by
        change (b ≫ Limits.pullback.fst _ _) ≫ (U i).hom =
          Spec.map (CommRingCat.ofHom e) ≫ s
        rw [← (f i).w]
        simp only [Category.assoc]
        rw [Limits.pullback.condition_assoc, x.w, ← Category.assoc, hb]
        rfl)
    refine ⟨i, L, hL, e, a, ?_⟩
    apply Over.OverMorphism.ext
    change (b ≫ Limits.pullback.fst _ _) ≫ (f i).left =
      Spec.map (CommRingCat.ofHom e) ≫ x.left
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hb]

private theorem density_scheme_etale {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : X.EtaleSite} (f : U ⟶ V) : Etale f.hom.left.left :=
  representable_etale_scheme_tests.2.2.2.2.2.2.2.2.2 X U.obj.left V.obj.left
    U.obj.hom V.obj.hom f.hom.left U.property V.property f.hom.w

private theorem density_cover_agreement {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : X.EtaleSite) (R : Presieve U) :
    R ∈ X.etalePrecoverage U ↔
      R.map (enlargedSchemeInclusion X) ∈
        X.enlargedEtalePrecoverage ((enlargedSchemeInclusion X).obj U) := by
  obtain ⟨I, V, a, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows, density_cover_iff]
  change _ ↔ IsJointlySurjective (fun i ↦ yoneda.map (a i).hom.left)
  rw [density_scheme_points]
  constructor
  · intro h x
    obtain ⟨W, f, ⟨i⟩, y, hy⟩ := h.2 x
    exact ⟨i, y, hy⟩
  · intro h
    refine ⟨fun _ f _ ↦ density_scheme_etale f, ?_⟩
    intro x
    obtain ⟨i, y, hy⟩ := h x
    exact ⟨V i, a i, ⟨i⟩, y, hy⟩

private theorem density_small_pullback {S : Scheme.{u}} (X : AlgebraicSpace S)
    {U V T : X.EtaleSite} (a : U ⟶ T) (b : V ⟶ T) :
    ∃ (W : X.EtaleSite) (p : W ⟶ U) (q : W ⟶ V),
      IsPullback p q a b ∧
      IsPullback ((enlargedSchemeInclusion X).map p)
        ((enlargedSchemeInclusion X).map q)
        ((enlargedSchemeInclusion X).map a) ((enlargedSchemeInclusion X).map b) := by
  let P := Limits.pullback a.hom.left b.hom.left
  let p : P ⟶ U.obj.left := Limits.pullback.fst _ _
  let q : P ⟶ V.obj.left := Limits.pullback.snd _ _
  have hq : Etale q.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback a.hom.left b.hom.left).map (Over.forget S))
    (density_scheme_etale a)
  have hqe : IsEtale (yoneda.map q) :=
    (representable_etale_scheme_tests.2.2.2.2.2.2.2.1 _ _ q).2 hq
  let W : X.EtaleSite := ⟨CostructuredArrow.mk (yoneda.map q ≫ V.obj.hom),
    isEtale_comp _ _ hqe V.property⟩
  let p' : W ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk p (by
    dsimp [p, q, W]
    rw [← CostructuredArrow.w a.hom, ← CostructuredArrow.w b.hom,
      ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      Limits.pullback.condition]))
  let q' : W ⟶ V := ObjectProperty.homMk (CostructuredArrow.homMk q (by rfl))
  have hi : IsPullback ((enlargedSchemeInclusion X).map p')
      ((enlargedSchemeInclusion X).map q')
      ((enlargedSchemeInclusion X).map a) ((enlargedSchemeInclusion X).map b) := by
    apply IsPullback.of_map_of_faithful (densityForget X)
    exact (IsPullback.of_hasPullback a.hom.left b.hom.left).map yoneda
  have := (density_fullyFaithful X).faithful
  have := (density_fullyFaithful X).full
  exact ⟨W, p', q', hi.of_map_of_faithful (enlargedSchemeInclusion X), hi⟩

/-- The displayed families satisfy the site axioms; the enlarged site has finite limits.
Source: Stacks, Tags 03G0 and 03G2
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the terminal object is `X/X`. Fibre products are sheaf fibre products, algebraic
by `fibreProduct_isAlgebraicSpace`. Chartwise étaleness is preserved by base change,
composition and cancellation (Tags 03FT--03FV). These facts also prove the identity,
composition and base-change covering axioms, including the empty covering. -/
theorem enlargedEtale_site (X : AlgebraicSpace S) :
    X.enlargedEtalePrecoverage.IsSiteForCoverings ∧ Nonempty (HasFiniteLimits X.EnlargedEtaleSite)
    := by
  have hsite := density_site X
  obtain ⟨T, _, ht⟩ := density_terminal X
  let : HasTerminal X.EnlargedEtaleSite := ht.some.hasTerminal
  let : ∀ {U V W : X.EnlargedEtaleSite} {f : U ⟶ W} {g : V ⟶ W},
      HasPullback f g := by
    intro U V W f g
    obtain ⟨P, p, q, h, _⟩ := density_pullbacks X U V W f g
    exact h.hasPullback
  let : HasPullbacks X.EnlargedEtaleSite := hasPullbacks_of_hasLimit_cospan _
  exact ⟨hsite, ⟨hasFiniteLimits_of_hasTerminal_and_pullbacks⟩⟩

/-- Scheme inclusion is continuous.
Source: Stacks, Tag 03G1 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the same scheme families cover in both sites, and scheme covering pullbacks
are the same fibre products. Precomposition therefore preserves sheaves. -/
theorem enlargedSchemeInclusion_continuous (X : AlgebraicSpace S) :
    (enlargedSchemeInclusion X).IsContinuous X.etaleTopology X.enlargedEtaleTopology := by
  let : ∀ {U V T : X.EtaleSite} {a : U ⟶ T} {b : V ⟶ T}, HasPullback a b := by
    intro U V T a b
    obtain ⟨P, p, q, h, _⟩ := density_small_pullback X a b
    exact h.hasPullback
  let : HasPullbacks X.EtaleSite := hasPullbacks_of_hasLimit_cospan _
  let : PreservesLimitsOfShape WalkingCospan (enlargedSchemeInclusion X) := by
    apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
    intro U V T a b _
    exact density_small_pullback X a b
  refine ⟨fun G ↦ ?_⟩
  rw [X.etalePrecoverage.isSheaf_toGrothendieck_iff]
  intro U V b R hR
  obtain ⟨I, T, a, rfl⟩ := R.exists_eq_ofArrows
  choose P p q hp hi using fun i ↦ density_small_pullback X b (a i)
  have hc : Presieve.ofArrows P p ∈ X.etalePrecoverage V := by
    apply (density_cover_agreement X V _).2
    rw [Presieve.map_ofArrows]
    exact density_cover_pullback X _ _ _ _ hi (by
      simpa only [Presieve.map_ofArrows] using (density_cover_agreement X U _).1 hR)
  rw [← Sieve.ofArrows, ← Sieve.ofArrows_eq_pullback_of_isPullback a hp,
    Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate]
  let : (enlargedSchemeInclusion X).PreservesPairwisePullbacks (Presieve.ofArrows P p) :=
    ⟨fun _ _ _ _ _ _ ↦ inferInstance⟩
  apply (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks
    (enlargedSchemeInclusion X) G.obj _).2
  exact ((isSheaf_iff_isSheaf_of_type _ _).1 G.property).isSheafFor_of_mem_precoverage
    ((density_cover_agreement X V _).1 hc)


attribute [instance] enlargedSchemeInclusion_continuous

/-- Restriction to scheme objects is literal precomposition.
Source: Stacks, Tags 03G1 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedRestriction (X : AlgebraicSpace S) (A : Type w) [Category.{v} A] :
    Sheaf X.enlargedEtaleTopology A ⥤ Sheaf X.etaleTopology A :=
  (enlargedSchemeInclusion X).sheafPushforwardContinuous A _ _

/-- Restriction is an equivalence of topoi, also for ring-valued sheaves.
Source: Stacks, Tags 03G1 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: scheme inclusion is fully faithful by Yoneda. It is continuous and cocontinuous:
refine a cover by choosing scheme atlases of its members. Every enlarged object has a
surjective étale scheme chart. The five comparison conditions therefore hold; apply
`specialCocontinuous_sheafEquivalence`. For rings lift each algebraic operation along
full faithfulness; the ring identities can be checked after faithful restriction
(`sheaves_algebraicStructures_objects`). -/
theorem enlargedRestriction_equivalence (X : AlgebraicSpace S) :
    (enlargedRestriction X (Type (max (u + 1) w))).IsEquivalence ∧
      (enlargedRestriction X RingCat.{u}).IsEquivalence := by
  sorry

/-- The canonical ring extension equivalence, with forward functor restriction.
Source: Stacks, Tag 03H7 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedRingEquivalence (X : AlgebraicSpace S) :
    Sheaf X.enlargedEtaleTopology RingCat.{u} ≌ Sheaf X.etaleTopology RingCat.{u} :=
  @Functor.asEquivalence _ _ _ _ (enlargedRestriction X RingCat.{u})
    (enlargedRestriction_equivalence.{u, 0} X).2

/-- The extended structure sheaf, obtained by the normalized inverse of restriction.
Source: Stacks, Tags 03H7 and 03G7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedStructureSheaf (X : AlgebraicSpace S) : Sheaf X.enlargedEtaleTopology RingCat.{u} :=
  (enlargedRingEquivalence X).inverse.obj X.structureSheaf

/-- Its specified restriction isomorphism.
Source: Stacks, Tag 03H7 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedStructureRestriction (X : AlgebraicSpace S) :
    (enlargedRestriction X RingCat.{u}).obj X.enlargedStructureSheaf ≅ X.structureSheaf :=
  (enlargedRingEquivalence X).counitIso.app X.structureSheaf

/-- Restriction of modules along the normalized structure-ring isomorphism.
Source: Stacks, Tag 03H7 and Modules on Sites, Tag 0409
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedModuleRestriction (X : AlgebraicSpace S) :
    ringedSiteModules.{max (u + 1) w} X.enlargedStructureSheaf ⥤
      ringedSiteModules.{max (u + 1) w} X.structureSheaf :=
  SheafOfModules.pushforward (enlargedStructureRestriction X).inv

/-- The same restriction gives the equivalence of module categories.
Source: Stacks, Tag 03H7 and the paragraph after Tag 03G7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: extend the underlying abelian sheaf by the comparison equivalence. Extend its
module action using preservation of products and full faithfulness. Addition, zero,
inverse, scalar laws and linearity of maps hold after faithful restriction, hence
before restriction. These constructions give inverse functors. -/
theorem enlargedModuleRestriction_equivalence (X : AlgebraicSpace S) :
    (enlargedModuleRestriction.{u, w} X).IsEquivalence := by
  sorry


/-- Extensions with specified restriction are unique up to unique normalized isomorphism.
Source: Stacks, Tags 03G1 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: full faithfulness of restriction lifts `e ≫ d⁻¹` uniquely. Faithfulness lifts
its inverse identities, and proves uniqueness with the prescribed restriction. -/
theorem enlargedExtension_unique (X : AlgebraicSpace S)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w)))
    (G H : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
    (e : (enlargedRestriction X _).obj G ≅ F)
    (d : (enlargedRestriction X _).obj H ≅ F) :
    ∃! a : G ≅ H, (enlargedRestriction X _).map a.hom ≫ d.hom = e.hom := by
  let R := enlargedRestriction X (Type (max (u + 1) w))
  have : R.IsEquivalence := (enlargedRestriction_equivalence X).1
  refine ⟨R.preimageIso (e ≪≫ d.symm), ?_, ?_⟩
  · simp [R]
  · intro a ha
    apply Iso.ext
    apply R.map_injective
    apply (cancel_mono d.hom).1
    simpa [R] using ha

/-- The extension equalizer on every surjective étale scheme chart.
The value of the bijection is precisely restriction to that chart, followed by `e`.
The displayed square also quantifies over every scheme presentation of the overlap.
Source: Stacks, Tag 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the chart is a singleton covering. Its overlap is a scheme by
`etale_fibreProduct_isScheme`; the sheaf condition is the equalizer for the two
projections. Transport its two scheme values along `e`. Uniqueness of gluing proves
the restriction formula for every chart; on common refinements it proves naturality
in the enlarged object and in the sheaf. -/
theorem enlargedExtension_equalizer (X : AlgebraicSpace S)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w)))
    (G : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
    (e : (enlargedRestriction X _).obj G ≅ F)
    (T : X.EnlargedEtaleSite) (T₀ T₁ : X.EtaleSite)
    (a : (enlargedSchemeInclusion X).obj T₀ ⟶ T)
    (ha : IsEtale a.hom.left.hom.hom ∧ IsSurjective a.hom.left.hom.hom)
    (p q : T₁ ⟶ T₀)
    (hsq : IsPullback ((enlargedSchemeInclusion X).map p)
      ((enlargedSchemeInclusion X).map q) a a) :
    ∃ b : G.obj.obj (op T) ≃
        {s : F.obj.obj (op T₀) // F.obj.map p.op s = F.obj.map q.op s},
      ∀ x, (b x).val = e.hom.hom.app (op T₀) (G.obj.map a.op x) := by
  classical
  let i := enlargedSchemeInclusion X
  have cover : Presieve.singleton a ∈ X.enlargedEtalePrecoverage T := by
    constructor
    · intro U b hb
      cases hb
      intro V c hc
      exact isEtale_comp _ _ hc ha.1
    · intro K _ s x
      obtain ⟨U, r, q, hq, hr⟩ := ha.2 (Over.mk s) (yonedaEquiv.symm x)
      have := hr
      obtain ⟨y, _⟩ := r.left.surjective (IsLocalRing.closedPoint K)
      let L : Type u := U.left.residueField y
      let instL : Field L := inferInstance
      let d : K →+* L := (Spec.preimage (U.left.fromSpecResidueField y ≫ r.left)).hom
      have hd : Spec.map (CommRingCat.ofHom d) =
          U.left.fromSpecResidueField y ≫ r.left := Spec.map_preimage _
      let t : Over.mk (Spec.map (CommRingCat.ofHom d) ≫ s) ⟶ U :=
        Over.homMk (U.left.fromSpecResidueField y) (by
          change U.left.fromSpecResidueField y ≫ U.hom =
            Spec.map (CommRingCat.ofHom d) ≫ s
          rw [hd, Category.assoc]
          exact congrArg (fun k ↦ U.left.fromSpecResidueField y ≫ k) (Over.w r).symm)
      have ht : t ≫ r = Over.homMk (Spec.map (CommRingCat.ofHom d)) rfl := by
        apply Over.OverMorphism.ext
        exact hd.symm
      refine ⟨⟨⟨i.obj T₀, a⟩, Presieve.singleton_self a⟩, L, instL, d,
        q.app _ t, ?_⟩
      have h := congrArg (fun k ↦ k.app
        (op (Over.mk (Spec.map (CommRingCat.ofHom d) ≫ s))) t) hq.w
      change a.hom.left.hom.hom.app _ (q.app _ t) =
        (yonedaEquiv.symm x).app _ (t ≫ r) at h
      change a.hom.left.hom.hom.app _ (q.app _ t) =
        T.obj.left.obj.obj.map (t ≫ r).op x at h
      rw [ht] at h
      exact h
  have sh : Presieve.IsSheafFor G.obj (Presieve.singleton a) :=
    ((isSheaf_iff_isSheaf_of_type X.enlargedEtaleTopology G.obj).1 G.property).isSheafFor _
      (X.enlargedEtalePrecoverage.generate_mem_toGrothendieck cover)
  have glue (s : G.obj.obj (op (i.obj T₀)))
      (hs : G.obj.map (i.map p).op s = G.obj.map (i.map q).op s) :
      ∃! x, G.obj.map a.op x = s := by
    apply (Presieve.isSheafFor_singleton.1 sh) s
    intro V b c hbc
    let l := hsq.lift b c hbc
    have hlp : l ≫ i.map p = b := hsq.lift_fst b c hbc
    have hlq : l ≫ i.map q = c := hsq.lift_snd b c hbc
    calc
      G.obj.map b.op s = G.obj.map l.op (G.obj.map (i.map p).op s) := by
        rw [← G.obj.map_comp_apply, ← op_comp, hlp]
      _ = G.obj.map l.op (G.obj.map (i.map q).op s) := congrArg (G.obj.map l.op) hs
      _ = G.obj.map c.op s := by rw [← G.obj.map_comp_apply, ← op_comp, hlq]
  have nh (b : T₁ ⟶ T₀) (s : G.obj.obj (op (i.obj T₀))) :
      e.hom.hom.app (op T₁) (G.obj.map (i.map b).op s) =
        F.obj.map b.op (e.hom.hom.app (op T₀) s) :=
    ConcreteCategory.congr_hom (e.hom.hom.naturality b.op) s
  have ni (b : T₁ ⟶ T₀) (s : F.obj.obj (op T₀)) :
      e.inv.hom.app (op T₁) (F.obj.map b.op s) =
        G.obj.map (i.map b).op (e.inv.hom.app (op T₀) s) :=
    ConcreteCategory.congr_hom (e.inv.hom.naturality b.op) s
  let b : G.obj.obj (op T) →
      {s : F.obj.obj (op T₀) // F.obj.map p.op s = F.obj.map q.op s} := fun x ↦
    ⟨e.hom.hom.app (op T₀) (G.obj.map a.op x), by
      rw [← nh, ← nh]
      congr 1
      rw [← G.obj.map_comp_apply, ← G.obj.map_comp_apply, ← op_comp, ← op_comp, hsq.w]⟩
  have hb : Function.Bijective b := by
    constructor
    · intro x y hxy
      apply (Presieve.isSeparatedFor_singleton.1 sh.isSeparatedFor)
      have h := congrArg Subtype.val hxy
      exact (((sheafToPresheaf _ _).mapIso e).app (op T₀)).toEquiv.injective h
    · intro s
      have hs : G.obj.map (i.map p).op (e.inv.hom.app (op T₀) s.val) =
          G.obj.map (i.map q).op (e.inv.hom.app (op T₀) s.val) := by
        rw [← ni, ← ni, s.property]
      obtain ⟨x, hx, _⟩ := glue (e.inv.hom.app (op T₀) s.val) hs
      refine ⟨x, Subtype.ext ?_⟩
      change e.hom.hom.app (op T₀) (G.obj.map a.op x) = s.val
      rw [hx]
      exact ConcreteCategory.congr_hom
        (((sheafToPresheaf _ _).mapIso e).inv_hom_id_app (op T₀)) s.val
  exact ⟨Equiv.ofBijective b hb, fun _ ↦ rfl⟩

/-- The canonical base-change functor `V ↦ X ×_Y V`, including its maps on arrows.
Source: Stacks, Tag 03G2 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedBaseChange {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.EnlargedEtaleSite ⥤ X.EnlargedEtaleSite where
  obj T := ⟨Over.mk (enlargedFibreProductFst f T.obj.hom),
    enlargedFibreProduct_chartwise f T⟩
  map {T U} a := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
    (Limits.pullback.map f.hom T.obj.hom.hom f.hom U.obj.hom.hom
      (𝟙 _) a.hom.left.hom (𝟙 _) (by simp)
      (congrArg InducedCategory.Hom.hom (Over.w a.hom).symm)))
    (by apply ObjectProperty.hom_ext; simp [enlargedFibreProductFst]))
  map_id T := by
    apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext; simp [enlargedFibreProduct]
  map_comp a b := by
    apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Limits.pullback.hom_ext <;> simp

private abbrev enlargedOver (A : AlgebraicSpace S) : A.EnlargedEtaleSite ⥤ Over A.obj :=
  ObjectProperty.ι _ ⋙ Over.post (ObjectProperty.ι _)

/-- Density identifies terminal objects and pullbacks with their ambient sheaf limits.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
private theorem enlargedOver_preserves (A : AlgebraicSpace S) :
    PreservesFiniteLimits (enlargedOver A) := by
  let _ : HasFiniteLimits A.EnlargedEtaleSite := (enlargedEtale_site A).2.some
  obtain ⟨T, hT, ht⟩ := density_terminal A
  have hterm : IsTerminal ((enlargedOver A).obj T) := by
    change IsTerminal ((Over.post (ObjectProperty.ι _)).obj T.obj)
    rw [hT]
    exact Over.mkIdTerminal
  let _ : PreservesLimit (Functor.empty.{0} A.EnlargedEtaleSite) (enlargedOver A) :=
    preservesLimit_of_preserves_limit_cone ht.some
      ((isLimitMapConeEmptyConeEquiv (enlargedOver A) T).symm hterm)
  let _ : PreservesLimitsOfShape (Discrete.{0} PEmpty) (enlargedOver A) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  let _ : PreservesLimitsOfShape WalkingCospan (enlargedOver A) := by
    apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
    intro U V W a b _
    obtain ⟨P, p, q, hp, hs⟩ := density_pullbacks A U V W a b
    refine ⟨P, p, q, hp, ?_⟩
    exact IsPullback.of_map_of_faithful (Over.forget A.obj) hs
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- Ambient slice pullback preserves limits, which the fully faithful inclusion reflects.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
private theorem enlargedBaseChange_preserves {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    PreservesFiniteLimits (enlargedBaseChange f) := by
  let _ := enlargedOver_preserves Y
  let e : enlargedBaseChange f ⋙ enlargedOver X ≅
      enlargedOver Y ⋙ Over.pullback f.hom :=
    NatIso.ofComponents (fun T ↦ Over.isoMk
      (pullbackSymmetry f.hom T.obj.hom.hom) (by
        change (pullbackSymmetry f.hom T.obj.hom.hom).hom ≫
          Limits.pullback.snd T.obj.hom.hom f.hom =
            Limits.pullback.fst f.hom T.obj.hom.hom
        simp)) (by
        intro T U a
        apply Over.OverMorphism.ext
        dsimp [enlargedOver, Over.post, enlargedBaseChange, Over.pullback]
        apply Limits.pullback.hom_ext <;> simp [Category.assoc])
  let _ : PreservesFiniteLimits (enlargedBaseChange f ⋙ enlargedOver X) :=
    preservesFiniteLimits_of_natIso e.symm
  let _ : (enlargedOver X).Full :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (Functor.FullyFaithful.over X (ObjectProperty.ι IsAlgebraicSpace)
        (ObjectProperty.fullyFaithfulι IsAlgebraicSpace))).full
  let _ : (enlargedOver X).Faithful :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (Functor.FullyFaithful.over X (ObjectProperty.ι IsAlgebraicSpace)
        (ObjectProperty.fullyFaithfulι IsAlgebraicSpace))).faithful
  let _ : ReflectsLimitsOfSize.{0, 0} (enlargedOver X) :=
    fullyFaithful_reflectsLimits _
  exact preservesFiniteLimits_of_reflects_of_preserves (enlargedBaseChange f) (enlargedOver X)

/-- A base-changed arrow is a pullback of the original arrow in ambient sheaves.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
private theorem baseChange_arrow_pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : Y.EnlargedEtaleSite} (a : U ⟶ V) :
    IsPullback ((enlargedBaseChange f).map a).hom.left.hom
      (pullback.snd f.hom U.obj.hom.hom)
      (pullback.snd f.hom V.obj.hom.hom) a.hom.left.hom := by
  have h : a.hom.left.hom ≫ V.obj.hom.hom = U.obj.hom.hom :=
    congrArg InducedCategory.Hom.hom (Over.w a.hom)
  have hfst : ((enlargedBaseChange f).map a).hom.left.hom ≫
      Limits.pullback.fst f.hom V.obj.hom.hom =
        Limits.pullback.fst f.hom U.obj.hom.hom := by
    simp [enlargedBaseChange]
  apply IsPullback.of_right (h₁₂ := Limits.pullback.fst f.hom V.obj.hom.hom)
    (h₂₂ := V.obj.hom.hom) (v₁₃ := f.hom)
  · rw [hfst, h]
    exact IsPullback.of_hasPullback f.hom U.obj.hom.hom
  · simp [enlargedBaseChange]
  · exact IsPullback.of_hasPullback f.hom V.obj.hom.hom

/-- Lift a covering witness across the ambient sheaf pullback after a field extension.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
private theorem enlargedBaseChange_covers {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : Y.EnlargedEtaleSite) (P : Presieve V)
    (hP : P ∈ Y.enlargedEtalePrecoverage V) :
    P.map (enlargedBaseChange f) ∈
      X.enlargedEtalePrecoverage ((enlargedBaseChange f).obj V) := by
  refine ⟨?_, ?_⟩
  · intro U a ha
    exact enlarged_chart_cancel _ _ _ _ _ a.hom.left
      U.property ((enlargedBaseChange f).obj V).property (Over.w a.hom)
  · intro K _ s x
    obtain ⟨i, L, hL, e, y, hy⟩ := hP.2 K s ((pullback.snd f.hom V.obj.hom.hom).hom.app _ x)
    let a := i.1.2
    have sq := ((sheafToPresheaf _ _).map_isPullback
      (baseChange_arrow_pullback f a)).app
        (op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s)))
    let t : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ Over.mk s :=
      Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl
    have heq : (pullback.snd f.hom V.obj.hom.hom).hom.app _
        (((enlargedBaseChange f).obj V).obj.left.obj.obj.map t.op x) =
          a.hom.left.hom.hom.app _ y := by
      rw [hy]
      exact ConcreteCategory.congr_hom
        ((pullback.snd f.hom V.obj.hom.hom).hom.naturality t.op) x
    obtain ⟨z, hz, _⟩ := Types.exists_of_isPullback sq _ _ heq
    exact ⟨⟨⟨_, (enlargedBaseChange f).map a⟩, Presieve.map_map i.2⟩,
      L, hL, e, z, hz⟩

/-- The base-change functor is continuous.
Source: Stacks, Tag 03G2(1)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: base change preserves chartwise étaleness and joint surjectivity. The
fibre-product universal property identifies covering pullbacks before and after base
change. Thus precomposition preserves the covering equalizers of every sheaf. -/
theorem enlargedBaseChange_continuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (enlargedBaseChange f).IsContinuous Y.enlargedEtaleTopology X.enlargedEtaleTopology := by
  let : HasFiniteLimits Y.EnlargedEtaleSite := (enlargedEtale_site Y).2.some
  let : PreservesFiniteLimits (enlargedBaseChange f) := enlargedBaseChange_preserves f
  refine ⟨fun G ↦ ?_⟩
  rw [Y.enlargedEtalePrecoverage.isSheaf_toGrothendieck_iff]
  intro U V b R hR
  obtain ⟨I, T, a, rfl⟩ := R.exists_eq_ofArrows
  choose P p q hp _ using fun i ↦ density_pullbacks Y V (T i) U b (a i)
  have hc : Presieve.ofArrows P p ∈ Y.enlargedEtalePrecoverage V :=
    density_cover_pullback Y a b p q hp hR
  rw [← Sieve.ofArrows, ← Sieve.ofArrows_eq_pullback_of_isPullback a hp,
    Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate]
  let : (enlargedBaseChange f).PreservesPairwisePullbacks (Presieve.ofArrows P p) :=
    ⟨fun _ _ _ _ _ _ ↦ inferInstance⟩
  apply (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks
    (enlargedBaseChange f) G.obj _).2
  exact ((isSheaf_iff_isSheaf_of_type _ _).1 G.property).isSheafFor_of_mem_precoverage
    (enlargedBaseChange_covers f V _ hc)


attribute [instance] enlargedBaseChange_continuous

/-- Direct image on enlarged sites is actual evaluation on fibre products.
Source: Stacks, Tag 03G2(1)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedDirectImage {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A : Type w) [Category.{v} A] :
    Sheaf X.enlargedEtaleTopology A ⥤ Sheaf Y.enlargedEtaleTopology A :=
  (enlargedBaseChange f).sheafPushforwardContinuous A _ _

/-- The base-change direct image has a left exact left adjoint.
Source: Stacks, Tag 03G2(1),(3)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the base-change functor preserves terminal objects and fibre products, hence
finite limits. Its left Kan extension followed by sheafification is left adjoint to
precomposition and left exact (Sites, Tag 00X6). Transfer through restriction to
obtain exactly the small étale geometric morphism of Tag 03G2(3). -/
theorem enlargedDirectImage_geometric {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃ g : GeometricMorphism (Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
        (Sheaf Y.enlargedEtaleTopology (Type (max (u + 1) w))),
      g.direct = enlargedDirectImage f _ := by
  let : HasFiniteLimits Y.EnlargedEtaleSite := (enlargedEtale_site Y).2.some
  let : PreservesFiniteLimits (enlargedBaseChange f) := enlargedBaseChange_preserves f
  let : RepresentablyFlat (enlargedBaseChange f) := flat_of_preservesFiniteLimits _
  have : AB5OfSize.{u + 1, u + 1} (Type (max (u + 1) w)) :=
    AB5OfSize_shrink.{u + 1, u + 1, max (u + 1) w, max (u + 1) w} _
  let L := (enlargedBaseChange f).sheafPullback (Type (max (u + 1) w))
    Y.enlargedEtaleTopology X.enlargedEtaleTopology
  let : PreservesFiniteLimits L := by
    dsimp [L]
    apply Functor.sheafPullbackConstruction.preservesFiniteLimits
  exact ⟨⟨L, enlargedDirectImage f _,
    (enlargedBaseChange f).sheafAdjunctionContinuous _ _ _, inferInstance⟩, rfl⟩



/-- A commuting pair of scheme charts maps canonically to the base-change object.
Source: Stacks, proof of Tag 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedChartLift {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : X.EtaleSite) (V : Y.EtaleSite) (g : U.obj.left ⟶ V.obj.left)
    (h : yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom) :
    (enlargedSchemeInclusion X).obj U ⟶
      (enlargedBaseChange f).obj ((enlargedSchemeInclusion Y).obj V) :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
    (Limits.pullback.lift (⟨U.obj.hom⟩ : (schemeSpace U.obj.left).obj ⟶ X.obj)
      ((Scheme.fppfTopology.over S).yoneda.map g)
      (by apply Sheaf.hom_ext; exact h.symm)))
    (by
      apply ObjectProperty.hom_ext
      change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ = _
      simp only [Limits.pullback.lift_fst]
      rfl))

/-- Normalization of the structural ring map: on every pair of commuting scheme charts
it is the usual pullback of regular functions, including the specified restriction isos.
Source: Stacks, Tag 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def IsEnlargedStructuralMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (r : Y.enlargedStructureSheaf ⟶
      (enlargedDirectImage f RingCat.{u}).obj X.enlargedStructureSheaf) : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (g : U.obj.left ⟶ V.obj.left)
    (h : yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom),
    (enlargedStructureRestriction Y).inv.hom.app (op V) ≫
      r.hom.app (op ((enlargedSchemeInclusion Y).obj V)) ≫
      X.enlargedStructureSheaf.obj.map (enlargedChartLift f U V g h).op ≫
      (enlargedStructureRestriction X).hom.hom.app (op U) =
        (forget₂ CommRingCat RingCat).map (Scheme.Γ.map g.left.op)

/-- The canonical ring map exists uniquely with its scheme-chart normalization.
Source: Stacks, Tag 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: for a scheme `V → Y`, pull functions back to a scheme atlas of `X ×_Y V`.
The two pullbacks on its overlap agree, so the equalizer glues a unique section.
A common refinement proves chart independence, naturality and the ring identities.
Full faithfulness of restriction extends this map to the enlarged site. Its values
on scheme charts force uniqueness by the equalizer and faithful restriction. -/
theorem enlargedStructuralMap_existsUnique {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃! r : Y.enlargedStructureSheaf ⟶
        (enlargedDirectImage f RingCat.{u}).obj X.enlargedStructureSheaf,
      IsEnlargedStructuralMap f r := by
  sorry

/-- The unique structural map specified on charts, in adjoint direct-image form.
Source: Stacks, Tag 03G8 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedStructuralMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.enlargedStructureSheaf ⟶
      (enlargedDirectImage f RingCat.{u}).obj X.enlargedStructureSheaf :=
  (enlargedStructuralMap_existsUnique f).choose

/-- Composition comparison is normalized by the two fibre-product projections;
the structural ring maps compose under exactly this comparison.
Source: Stacks, Tags 03G2(2) and 03G8(1)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the unique map preserving the projections identifies
`W ×_X (X ×_Y V)` with `W ×_Y V`. Its inverse and naturality follow from the same
universal property. Precomposition identifies direct images; uniqueness of left
adjoints gives the adjunction-compatible inverse-image comparison
(`siteMorphism_composition`). On scheme charts both ring maps pull regular functions
back along the same composite. Their equalizers imply the displayed equality.
For three maps each comparison has the same projections, giving coherence. -/
theorem enlargedBaseChange_composition {W X Y : AlgebraicSpace S}
    (g : W ⟶ X) (f : X ⟶ Y) :
    ∃ c : enlargedBaseChange f ⋙ enlargedBaseChange g ≅ enlargedBaseChange (g ≫ f),
      (∀ V : Y.EnlargedEtaleSite,
        (c.hom.app V).hom.left.hom ≫ Limits.pullback.fst (g ≫ f).hom V.obj.hom.hom =
          Limits.pullback.fst g.hom (enlargedFibreProductFst f V.obj.hom).hom) ∧
      (∀ V : Y.EnlargedEtaleSite,
        (c.hom.app V).hom.left.hom ≫ Limits.pullback.snd (g ≫ f).hom V.obj.hom.hom =
          Limits.pullback.snd g.hom (enlargedFibreProductFst f V.obj.hom).hom ≫
            Limits.pullback.snd f.hom V.obj.hom.hom) ∧
      ∀ V : Y.EnlargedEtaleSite,
        (enlargedStructuralMap f).hom.app (op V) ≫
          (enlargedStructuralMap g).hom.app (op ((enlargedBaseChange f).obj V)) ≫
          W.enlargedStructureSheaf.obj.map (c.inv.app V).op =
            (enlargedStructuralMap (g ≫ f)).hom.app (op V) := by
  sorry

/-- Identity comparison and its structural ring-map normalization.
Source: Stacks, Tags 03G2 and 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: `X ×_X V → V` is the second projection, with inverse the graph. The
structural map restricts to the identity on every scheme chart; equalizer descent
gives the equality on every enlarged object. -/
theorem enlargedBaseChange_identity (X : AlgebraicSpace S) :
    ∃ c : enlargedBaseChange (𝟙 X) ≅ 𝟭 X.EnlargedEtaleSite,
      (∀ V : X.EnlargedEtaleSite,
        (c.hom.app V).hom.left.hom = Limits.pullback.snd (𝟙 X : X ⟶ X).hom V.obj.hom.hom) ∧
      ∀ V : X.EnlargedEtaleSite,
        (enlargedStructuralMap (𝟙 X)).hom.app (op V) =
          X.enlargedStructureSheaf.obj.map (c.hom.app V).op := by
  let c : enlargedBaseChange (𝟙 X) ≅ 𝟭 X.EnlargedEtaleSite :=
    NatIso.ofComponents
      (fun V ↦ ObjectProperty.isoMk _ (Over.isoMk
        (ObjectProperty.isoMk _ (asIso (Limits.pullback.snd (𝟙 X.obj) V.obj.hom.hom)))
        (by
          apply ObjectProperty.hom_ext
          change Limits.pullback.snd (𝟙 X.obj) V.obj.hom.hom ≫ V.obj.hom.hom =
            Limits.pullback.fst (𝟙 X.obj) V.obj.hom.hom
          simpa using (Limits.pullback.condition (f := 𝟙 X.obj)
            (g := V.obj.hom.hom)).symm)))
      (by
        intro V V' a
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        simp [enlargedBaseChange])
  let r : X.enlargedStructureSheaf ⟶
      (enlargedDirectImage (𝟙 X) RingCat.{u}).obj X.enlargedStructureSheaf :=
    ⟨Functor.whiskerRight (NatTrans.op c.hom) X.enlargedStructureSheaf.obj⟩
  have hr : IsEnlargedStructuralMap (𝟙 X) r := by
    intro U V g h
    let m : U ⟶ V := ObjectProperty.homMk (CostructuredArrow.homMk g (by simpa using h))
    have hc : enlargedChartLift (𝟙 X) U V g h ≫
        c.hom.app ((enlargedSchemeInclusion X).obj V) =
          (enlargedSchemeInclusion X).map m := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
      simp only [Limits.pullback.lift_snd]
      rfl
    change (enlargedStructureRestriction X).inv.hom.app (op V) ≫
      X.enlargedStructureSheaf.obj.map
        (c.hom.app ((enlargedSchemeInclusion X).obj V)).op ≫
      X.enlargedStructureSheaf.obj.map (enlargedChartLift (𝟙 X) U V g h).op ≫
      (enlargedStructureRestriction X).hom.hom.app (op U) = _
    rw [← Functor.map_comp_assoc, ← op_comp, hc]
    change (enlargedStructureRestriction X).inv.hom.app (op V) ≫
      ((enlargedRestriction X RingCat.{u}).obj X.enlargedStructureSheaf).obj.map m.op ≫
      (enlargedStructureRestriction X).hom.hom.app (op U) = _
    rw [(enlargedStructureRestriction X).hom.hom.naturality m.op]
    simp only [← Category.assoc]
    have hi : (enlargedStructureRestriction X).inv.hom.app (op V) ≫
        (enlargedStructureRestriction X).hom.hom.app (op V) =
          𝟙 (X.structureSheaf.obj.obj (op V)) :=
      ((sheafToPresheaf _ _).mapIso (enlargedStructureRestriction X)).inv_hom_id_app (op V)
    change ((enlargedStructureRestriction X).inv.hom.app (op V) ≫
      (enlargedStructureRestriction X).hom.hom.app (op V)) ≫
      X.structureSheaf.obj.map m.op = X.structureSheaf.obj.map m.op
    rw [hi, Category.id_comp]
  have heq : enlargedStructuralMap (𝟙 X) = r :=
    (enlargedStructuralMap_existsUnique (𝟙 X)).choose_spec.2 r hr |>.symm
  refine ⟨c, fun _ ↦ rfl, ?_⟩
  intro V
  rw [heq]
  rfl


/-- An étale space is an object of the enlarged site.
Source: Stacks, Tags 03G0 and 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedEtaleObject {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    Y.EnlargedEtaleSite := ⟨Over.mk f, hf⟩

/-- Postcomposition by an étale map, retaining the same underlying spaces and arrows.
Source: Stacks, Tags 03LP and 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedPostcompose {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    X.EnlargedEtaleSite ⥤ Y.EnlargedEtaleSite :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Over.map f)
    (fun T ↦ enlargedEtale_comp T.obj.hom f T.property hf)

/-- Postcomposition with an étale map, with its factorization remembered in the slice.
Source: Stacks, Tag 04LY (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedLocalization {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    X.EnlargedEtaleSite ⥤ Over (enlargedEtaleObject f hf) where
  obj T := Over.mk (ObjectProperty.homMk
    (Over.homMk T.obj.hom : ((enlargedPostcompose f hf).obj T).obj ⟶
      (enlargedEtaleObject f hf).obj))
  map a := Over.homMk ((enlargedPostcompose f hf).map a)
    (by apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext; exact Over.w a.hom)
  map_id T := by rfl
  map_comp a b := by rfl


/-- Postcomposition identifies the enlarged site with its localization, preserving
exactly the covering sieves. Source: Stacks, Tag 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: an arrow `T → X` étale over `X` is étale over `Y` by composition. Conversely,
a factorization `T → X → Y` of two objects étale over `Y` has its first arrow étale
by cancellation (Tag 03FV). These functors are inverse before taking representatives.
Their covering families are precisely the same jointly surjective arrows. Passing to
the generated topologies gives the displayed equality of covering sieves. -/
theorem enlargedLocalization_equivalence {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    (enlargedLocalization f hf).IsEquivalence ∧
      ∀ (T : X.EnlargedEtaleSite) (R : Sieve T),
        R ∈ X.enlargedEtaleTopology T ↔
          R.functorPushforward (enlargedLocalization f hf) ∈
            (Y.enlargedEtaleTopology.over (enlargedEtaleObject f hf))
              ((enlargedLocalization f hf).obj T) := by
  sorry

/-- Postcomposition is continuous and therefore defines literal restriction of sheaves.
Source: Stacks, Tag 03LP and Tag 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: use the localization equivalence and its covering-sieve comparison to prove
continuity of localization. Postcomposition factors through localization followed by
the continuous slice forgetful functor. Composition gives the claimed continuity. -/
theorem enlargedPostcompose_continuous {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    (enlargedPostcompose f hf).IsContinuous X.enlargedEtaleTopology
      Y.enlargedEtaleTopology := by
  let L := enlargedLocalization f hf
  let J := Y.enlargedEtaleTopology.over (enlargedEtaleObject f hf)
  have hL := enlargedLocalization_equivalence f hf
  have : L.IsEquivalence := hL.1
  have : L.IsContinuous X.enlargedEtaleTopology J :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfDownwardsClosed J L (fun {_ d} _ ↦
        ⟨L.objPreimage d, L.objObjPreimageIso d⟩))
      ⟨fun {T R} hR ↦ (hL.2 T R).1 hR⟩
  change (L ⋙ Over.forget (enlargedEtaleObject f hf)).IsContinuous
    X.enlargedEtaleTopology Y.enlargedEtaleTopology
  exact Functor.isContinuous_comp L (Over.forget _) _ J _

attribute [instance] enlargedPostcompose_continuous

/-- Restriction along an étale map, i.e. localization inverse image.
Source: Stacks, Tags 03LP and 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedEtaleRestriction {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : IsChartwiseEtale f) (A : Type w) [Category.{v} A] :
    Sheaf Y.enlargedEtaleTopology A ⥤ Sheaf X.enlargedEtaleTopology A :=
  (enlargedPostcompose f hf).sheafPushforwardContinuous A _ _

/-- Chartwise étaleness suffices for postcomposition on the scheme small sites.
Source: Stacks, Tag 03LP
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def chartwiseEtaleMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    X.EtaleSite ⥤ Y.EtaleSite :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ CostructuredArrow.map f.hom.hom)
    (fun T ↦ hf T.obj.left T.obj.hom T.property)

/-- The scheme inclusions commute with étale postcomposition; the comparison is
identity on underlying scheme sheaves. Source: Stacks, proof of Tag 03LP
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedPostcomposeSchemeIso {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    chartwiseEtaleMap f hf ⋙ enlargedSchemeInclusion Y ≅
      enlargedSchemeInclusion X ⋙ enlargedPostcompose f hf :=
  Iso.refl _

/-- Restriction and base-change direct image are the localization adjunction;
the structural ring map is its unit under the normalized structure-ring identification.
Source: Stacks, Tags 03LP, 04LY and 04LZ
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: `slice_subtopos_site_presentation` identifies inverse image with restriction
and direct image with evaluation on products with `X/Y`. Under `enlargedLocalization`
those products are the fibre products in `enlargedBaseChange`. Sectionwise limits
show that restriction is left exact. The restricted ring and the extended ring of
`X` both evaluate to `Γ(U,O_U)` on every scheme chart, with the same restrictions.
Full faithfulness gives the unique ring isomorphism inducing the identity on these
sections. The ring unit followed by this isomorphism pulls functions back along the
projection on every chart, and so equals the unique structural map globally. -/
theorem enlargedEtale_localization {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    Nonempty (enlargedEtaleRestriction f hf (Type (max (u + 1) w)) ⊣
      enlargedDirectImage f (Type (max (u + 1) w))) ∧
    PreservesFiniteLimits (enlargedEtaleRestriction f hf (Type (max (u + 1) w))) ∧
    ∃ ar : enlargedEtaleRestriction f hf RingCat.{u} ⊣ enlargedDirectImage f RingCat.{u},
      ∃ e : (enlargedEtaleRestriction f hf RingCat.{u}).obj Y.enlargedStructureSheaf ≅
          X.enlargedStructureSheaf,
        (∀ U : X.EtaleSite,
          (enlargedStructureRestriction Y).inv.hom.app (op ((chartwiseEtaleMap f hf).obj U)) ≫
            Y.enlargedStructureSheaf.obj.map ((enlargedPostcomposeSchemeIso f hf).inv.app U).op ≫
            e.hom.hom.app (op ((enlargedSchemeInclusion X).obj U)) ≫
            (enlargedStructureRestriction X).hom.hom.app (op U) = 𝟙 _) ∧
        ar.unit.app Y.enlargedStructureSheaf ≫
          (enlargedDirectImage f RingCat.{u}).map e.hom = enlargedStructuralMap f := by
  sorry

/-- Every surjective étale scheme chart has a scheme overlap, in the enlarged site.
Source: Stacks, Tag 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: apply the chart's representable étale scheme test along itself. Its scheme
projection is étale, hence its composite to `X` is an object of the small site.
Yoneda lifts the other projection, and the square's equation is also its equation
over `X`. Reflect this presheaf pullback through the sheaf and full-subcategory
inclusions and the over-category forgetful functor to obtain the asserted square. -/
theorem enlargedChartOverlap_exists (X : AlgebraicSpace S)
    (T : X.EnlargedEtaleSite) (T₀ : X.EtaleSite)
    (a : (enlargedSchemeInclusion X).obj T₀ ⟶ T)
    (ha : IsEtale a.hom.left.hom.hom ∧ IsSurjective a.hom.left.hom.hom) :
    ∃ (T₁ : X.EtaleSite) (p q : T₁ ⟶ T₀),
      IsPullback ((enlargedSchemeInclusion X).map p)
        ((enlargedSchemeInclusion X).map q) a a := by
  obtain ⟨U, p, q, hq, hp⟩ := ha.1 T₀.obj.left a.hom.left.hom.hom
  let r : U ⟶ T₀.obj.left := yoneda.preimage q
  have hr : yoneda.map r = q := yoneda.map_preimage q
  have hw : a.hom.left.hom.hom ≫ T.obj.hom.hom.hom = T₀.obj.hom :=
    congrArg (fun k ↦ k.hom.hom) (Over.w a.hom)
  have hqr : yoneda.map r ≫ T₀.obj.hom = yoneda.map p ≫ T₀.obj.hom := by
    rw [← hw, ← Category.assoc, ← Category.assoc, hr, hq.w]
  have hpe : IsEtale (yoneda.map p) :=
    ((representable_etale_scheme_tests (S := S)).2.2.2.2.2.2.2.1 U T₀.obj.left p).2 hp
  let V : X.EtaleSite := ⟨CostructuredArrow.mk (yoneda.map p ≫ T₀.obj.hom),
    isEtale_comp _ _ hpe T₀.property⟩
  let p' : V ⟶ T₀ := ObjectProperty.homMk (CostructuredArrow.homMk r hqr)
  let q' : V ⟶ T₀ := ObjectProperty.homMk (CostructuredArrow.homMk p (by rfl))
  let forget := ObjectProperty.ι (fun A : Over X ↦ IsChartwiseEtale A.hom) ⋙
    Over.forget X ⋙ ObjectProperty.ι _ ⋙
      sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)
  refine ⟨V, p', q', ?_⟩
  apply IsPullback.of_map_of_faithful forget
  change IsPullback (yoneda.map r) (yoneda.map p) a.hom.left.hom.hom a.hom.left.hom.hom
  simpa only [hr] using hq


/-- The set-sheaf comparison equivalence has literal restriction as forward functor.
Source: Stacks, Tag 03G1 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedSetEquivalence (X : AlgebraicSpace S) :
    Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)) ≌
      Sheaf X.etaleTopology (Type (max (u + 1) w)) :=
  @Functor.asEquivalence _ _ _ _ (enlargedRestriction X (Type (max (u + 1) w)))
    (enlargedRestriction_equivalence X).1

/-- Direct image on the small étale topoi, transported along the scheme comparisons.
Source: Stacks, Tag 03G2(3)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedSmallDirectImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf X.etaleTopology (Type (max (u + 1) w)) ⥤
      Sheaf Y.etaleTopology (Type (max (u + 1) w)) :=
  (enlargedSetEquivalence X).inverse ⋙ enlargedDirectImage f _ ⋙
    (enlargedSetEquivalence Y).functor

/-- The small étale morphism is the transport of the enlarged-site geometric morphism.
Source: Stacks, Tag 03G2(3)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: compose the enlarged geometric morphism with the two comparison equivalences.
Their inverse functors are adjoint and preserve limits, so the composite is geometric.
Its direct image is the displayed transported evaluation-on-fibre-products functor. -/
theorem enlargedSmallDirectImage_geometric {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃ g : GeometricMorphism (Sheaf X.etaleTopology (Type (max (u + 1) w)))
        (Sheaf Y.etaleTopology (Type (max (u + 1) w))),
      g.direct = enlargedSmallDirectImage f := by
  obtain ⟨g, hg⟩ := enlargedDirectImage_geometric.{u, w} f
  let eX := enlargedSetEquivalence.{u, w} X
  let eY := enlargedSetEquivalence.{u, w} Y
  let gX : GeometricMorphism _ _ :=
    ⟨eX.functor, eX.inverse, eX.toAdjunction, inferInstance⟩
  let gY : GeometricMorphism _ _ :=
    ⟨eY.inverse, eY.functor, eY.symm.toAdjunction, inferInstance⟩
  refine ⟨(gX.comp g).comp gY, ?_⟩
  change (eX.inverse ⋙ g.direct) ⋙ eY.functor = _
  rw [hg]
  rfl


/-- Every small-site sheaf has an extension with a specified restriction isomorphism.
Source: Stacks, Tag 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: essential surjectivity of the restriction equivalence supplies the extension.
The chosen isomorphism is retained, so `enlargedExtension_unique` applies to it. -/
theorem enlargedExtension_exists (X : AlgebraicSpace S)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w))) :
    ∃ G : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)),
      Nonempty ((enlargedRestriction X _).obj G ≅ F) := by
  exact ⟨(enlargedSetEquivalence X).inverse.obj F,
    ⟨(enlargedSetEquivalence X).counitIso.app F⟩⟩

end AlgebraicGeometry.AlgebraicSpace
