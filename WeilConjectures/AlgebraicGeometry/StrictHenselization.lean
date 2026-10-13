/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Strict henselization from affine pointed neighbourhoods

Source: Weil conjectures blueprint, `sec-curve-estimates/sk-prop-h2`, definition
`def-weil-pbc-strict-henselization-limit` (blueprint: def-weil-pbc-strict-henselization-limit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Affine pointed neighbourhoods written as spectra of rings.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit).
The category of elements gives the lift of the geometric point and pointed morphisms. -/
abbrev strictHenselizationNeighbourhoods
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :=
  (AffineEtale.Spec S ⋙ (pointSmallEtale s).fiber).Elements

/-- The representative functor to the full affine pointed-neighbourhood category.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable def strictHenselizationAffineInclusion
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    strictHenselizationNeighbourhoods s ⥤ ObjectProperty.FullSubcategory
      (fun n : (pointSmallEtale s).fiber.Elements => IsAffine n.1.left) :=
  ObjectProperty.lift _
    (Functor.Elements.precomp (AffineEtale.Spec S) (pointSmallEtale s).fiber)
    (fun _ => inferInstanceAs (IsAffine (Spec _)))

/-- The ring-written affine pointed neighbourhoods represent every affine pointed
neighbourhood, fully faithfully.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit).

Proof: the spectrum functor from affine étale objects is fully faithful, so its
pointed category-of-elements functor is fully faithful as well. For an affine
pointed neighbourhood `(V,v)`, the affine scheme--ring equivalence gives
`V ≅ Spec Γ(V,top)`. Compose its structure morphism with the inverse of this
isomorphism and transport `v` along the isomorphism. This gives an affine étale
ring-object with the original pointed neighbourhood as its image up to isomorphism.
Thus the functor is essentially surjective, hence an equivalence. -/
theorem strictHenselizationAffineInclusion_isEquivalence
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    (strictHenselizationAffineInclusion s).IsEquivalence := by
  classical
  let F := AffineEtale.Spec S
  let G := (pointSmallEtale s).fiber
  have : (Functor.Elements.precomp F G).Faithful := ⟨by
    intro X Y f g h
    apply Subtype.ext
    exact F.map_injective (congrArg Subtype.val h)⟩
  have : (Functor.Elements.precomp F G).Full := ⟨fun {X Y} f ↦
    ⟨⟨F.preimage f.val, by
      change G.map (F.map (F.preimage f.val)) X.snd = Y.snd
      erw [F.map_preimage]
      exact f.property⟩, by
      apply Subtype.ext
      exact F.map_preimage f.val⟩⟩
  have : (strictHenselizationAffineInclusion s).Faithful := by
    unfold strictHenselizationAffineInclusion
    infer_instance
  have : (strictHenselizationAffineInclusion s).Full := by
    unfold strictHenselizationAffineInclusion
    infer_instance
  have : (strictHenselizationAffineInclusion s).EssSurj := by
    refine ⟨fun X ↦ ?_⟩
    let V := X.obj.fst
    have : IsAffine V.left := X.property
    let e := V.left.isoSpec
    let A : AffineEtale S := AffineEtale.mk (e.inv ≫ V.hom)
    let y : G.obj (F.obj A) := Over.homMk (X.obj.snd.left ≫ e.hom) (by
      change (X.obj.snd.left ≫ e.hom) ≫ (e.inv ≫ V.hom) = s
      rw [Category.assoc, e.hom_inv_id_assoc]
      exact Over.w X.obj.snd)
    refine ⟨(F ⋙ G).elementsMk A y, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    let i : F.obj A ≅ V := MorphismProperty.Over.isoMk e.symm rfl
    refine CategoryOfElements.isoMk _ _ i ?_
    apply Over.OverMorphism.ext
    change (X.obj.snd.left ≫ e.hom) ≫ e.inv = X.obj.snd.left
    erw [Category.assoc, e.hom_inv_id, Category.comp_id]
  exact { }

/-- The coordinate-ring diagram on all affine pointed neighbourhoods, contravariantly
sending a pointed map to its map on global sections.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable def strictHenselizationCoordinateRings
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : (strictHenselizationNeighbourhoods s)ᵒᵖ ⥤ CommRingCat.{u} :=
  (CategoryOfElements.π _ ⋙ AffineEtale.Spec S ⋙ Etale.forget S ⋙ Over.forget S).op ⋙ Γ

/-- The ring diagram on the chosen small representative category.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable def smallStrictHenselizationDiagram
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    (SmallModel.{u} (strictHenselizationNeighbourhoods s))ᵒᵖ ⥤ CommRingCat.{u} :=
  (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.op ⋙
    strictHenselizationCoordinateRings s

/-- Choose a small representative category of affine pointed neighbourhoods and take
its opposite-indexed coordinate-ring colimit. `SmallModel` supplies a fully faithful,
essentially surjective representative functor, so no affine neighbourhood is omitted.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable abbrev strictHenselizationRing
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : CommRingCat.{u} :=
  strictHenselization s

/-- Canonical comparison from the small ring-written diagram to upstream's affine diagram. -/
noncomputable def smallStrictHenselizationColimitIso
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    colimit (smallStrictHenselizationDiagram s) ≅ strictHenselization s := by
  let : HasColimit (strictHenselizationDiagram s) := inferInstance
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s
  let : (strictHenselizationAffineInclusion s).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence s
  exact Functor.Final.colimitIso F.op (strictHenselizationDiagram s)

/-- The small affine diagram's cocone with upstream's strict henselization as vertex. -/
noncomputable def smallStrictHenselizationCocone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Cocone (smallStrictHenselizationDiagram s) :=
  (colimit.cocone (strictHenselizationDiagram s)).whisker
    ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
      strictHenselizationAffineInclusion s).op

noncomputable def isColimitSmallStrictHenselizationCocone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : IsColimit (smallStrictHenselizationCocone s) := by
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s
  let : (strictHenselizationAffineInclusion s).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence s
  exact (Functor.Final.isColimitWhiskerEquiv F.op _).symm
    (colimit.isColimit (strictHenselizationDiagram s))

/-- The strict henselization scheme is the spectrum of the coordinate-ring colimit.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable abbrev strictHenselizationScheme
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Scheme.{u} :=
  strictLocalization s

/-- The canonical cone has vertex the strict henselization scheme; its legs are
`Spec.map` of the coordinate-ring colimit coprojections.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable def strictHenselizationCone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Cone ((smallStrictHenselizationDiagram s).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (smallStrictHenselizationCocone s).op

/-- Cofilteredness and the inverse-limit interpretation of the canonical cone.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit).

Proof: the affine pointed category is equivalent to the full affine subcategory of
pointed neighbourhoods, using the affine scheme--ring anti-equivalence. That full
subcategory is initial by `lemma-weil-pbc-affine-neighbourhood-cofinal`. The ambient
category is cofiltered by `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`;
`lem-weil-pbc-colimit-initial-full-subcategory` transfers cofilteredness to the affine
subcategory and then to the small representative model.
The opposite of the ring colimit cocone is a limit cone. The spectrum functor is a
right adjoint (`Spec.reflective`), hence carries this cone to a limit cone of schemes.
Its legs are exactly the spectra of the colimit coprojections
(`lem-weil-pbc-spec-small-colimit-limit`). The affine scheme--ring equivalence identifies
each spectrum of global sections with its original affine neighbourhood; transport
along the representative functor `(equivSmallModel _).inverse ⋙
strictHenselizationAffineInclusion s`, an equivalence by
`strictHenselizationAffineInclusion_isEquivalence`, gives the inverse limit over all
affine pointed neighbourhoods. -/
theorem strictHenselization_properties
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Functor.Initial ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
      strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements => IsAffine n.1.left)) ∧
      IsCofiltered (SmallModel.{u} (strictHenselizationNeighbourhoods s)) ∧
      Nonempty (IsLimit (strictHenselizationCone s)) := by
  classical
  have := strictHenselizationAffineInclusion_isEquivalence s
  have : (ObjectProperty.ι
      (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)).Initial :=
    AffinePointedEtaleNeighborhood.initial_ι s
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (pointSmallEtale s).fiber.Elements => IsAffine n.1.left)
  have : F.Initial := by dsimp [F]; infer_instance
  refine ⟨this, ?_, ?_⟩
  · apply IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful F
    intro X
    obtain ⟨Y⟩ := (inferInstance : Nonempty (CostructuredArrow F X))
    exact ⟨Y.left, ⟨Y.hom⟩⟩
  · exact ⟨isLimitOfPreserves Scheme.Spec
      (isColimitSmallStrictHenselizationCocone s).op⟩

/-- Independence of the representative category, via the canonical colimit map.
Here `e` describes a replacement of the chosen representative category and `w`
identifies its coordinate-ring diagram with the transported chosen diagram.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit).
The equivalence-colimit isomorphism has coprojection formula
`ι k ≫ iso.hom = D.map (e.unit.app k) ≫ w.inv.app _ ≫ ι _`
(`HasColimit.ι_isoOfEquivalence_hom`), so this is the canonical comparison.
It is an isomorphism by the equivalence-colimit lemma cited in the node. -/
noncomputable def strictHenselizationRepresentativeIso
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {J : Type u} [SmallCategory J]
    (e : J ≌ (SmallModel.{u} (strictHenselizationNeighbourhoods s))ᵒᵖ)
    (D : J ⥤ CommRingCat.{u}) (w : e.functor ⋙ smallStrictHenselizationDiagram s ≅ D) :
    colimit D ≅ strictHenselizationRing s :=
  HasColimit.isoOfEquivalence e w ≪≫ smallStrictHenselizationColimitIso s

end AlgebraicGeometry.Scheme
