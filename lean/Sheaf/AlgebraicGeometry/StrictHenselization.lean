/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.Ring.Colimits
public import Sheaf.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal

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
  sorry

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
noncomputable def strictHenselizationDiagram
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
noncomputable def strictHenselizationRing
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : CommRingCat.{u} :=
  colimit (strictHenselizationDiagram s)

/-- The strict henselization scheme is the spectrum of the coordinate-ring colimit.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable def strictHenselizationScheme
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Scheme.{u} :=
  Spec (strictHenselizationRing s)

/-- The canonical cone has vertex the strict henselization scheme; its legs are
`Spec.map` of the coordinate-ring colimit coprojections.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable def strictHenselizationCone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Cone ((strictHenselizationDiagram s).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (colimit.cocone (strictHenselizationDiagram s)).op

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
  sorry

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
    (D : J ⥤ CommRingCat.{u}) (w : e.functor ⋙ strictHenselizationDiagram s ≅ D) :
    colimit D ≅ strictHenselizationRing s :=
  HasColimit.isoOfEquivalence e w

end AlgebraicGeometry.Scheme
