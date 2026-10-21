/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q71 and Q7
-/
module

public import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

import Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange
import Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence
import Sheaf.SixFunctors.SmoothDualityBaseChangeCompat
import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
import Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal

/-! # Counit-normalized exceptional comparisons for section families

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-dnc, opening fibre restrictions,
Local construction and Gluing (blueprint: lem-trf-section-exceptional-fibre-coherence).

The records below package the geometric diagrams, not their cohomological comparisons.
Every comparison is constructed from the existing counit mate or the unique counit-normalized
locality isomorphism. The two fibre labels are `false` (zero) and `true` (one).
-/

@[expose] public section

set_option autoImplicit false


universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- A smooth compactifiable map with a closed section, as in the opening fibre restrictions
of blueprint sk-thm-dnc (blueprint: lem-trf-section-exceptional-fibre-coherence).
This is only a record of the geometric hypotheses; it contains no comparison maps. -/
structure ExceptionalSectionPair (B : Scheme.{u}) (d : ℕ) where
  total : Scheme.{u}
  map : total ⟶ B
  sect : B ⟶ total
  section_map : sect ≫ map = 𝟙 B
  [base_noetherian : IsNoetherian B]
  [total_noetherian : IsNoetherian total]
  [compactifiable : HasCompactification map]
  [separated : IsSeparated map]
  [smooth : SmoothOfRelativeDimension d map]
  [closed : IsClosedImmersion sect]

attribute [instance] ExceptionalSectionPair.total_noetherian ExceptionalSectionPair.compactifiable
  ExceptionalSectionPair.separated ExceptionalSectionPair.smooth ExceptionalSectionPair.closed

/-- A Cartesian change of a section pair, including the compatibility of the sections.
Source: blueprint sk-thm-dnc, fibre restrictions and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
structure ExceptionalSectionChange {B B' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionPair B d) (P' : ExceptionalSectionPair B' d) (v : B' ⟶ B) where
  upper : P'.total ⟶ P.total
  square : IsPullback upper P'.map P.map v
  section_comm : P'.sect ≫ upper = v ≫ P.sect

/-- Pullback along the two equal composites in a commuting square, using the canonical
inverse-image compositors. Source: blueprint sk-thm-dnc, Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def sectionCoherencePullbackIso
    (A : Type (u + 1)) [CommRing A]
    {B B' X X' : Scheme.{u}} (v : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X')
    (r : X' ⟶ X) (h : v ≫ i = i' ≫ r) (K : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor.obj K) ≅
      (upperStar (ModuleCat.{u + 1} A) i').leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v i).symm.app K ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i' r (v ≫ i) h).app K

private theorem sectionPullback_endpoint
    (A : Type (u + 1)) [CommRing A]
    {B B' X X' : Scheme.{u}} (v : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X')
    (r : X' ⟶ X) (z z' : B' ⟶ X)
    (h₁ : z = v ≫ i) (h₂ : z = i' ≫ r)
    (h₁' : z' = v ≫ i) (h₂' : z' = i' ≫ r) (K : DerivedCategoryModule A X) :
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v i z h₁).symm ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i' r z h₂).app K =
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v i z' h₁').symm ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i' r z' h₂').app K := by
  subst z
  subst z'
  rfl

/-- Section pullback of the actual counit-defined exceptional comparison at the coefficient
unit. Source: blueprint sk-thm-dnc, opening fibre restrictions
(blueprint: lem-trf-section-exceptional-fibre-coherence). The input map is the existing
`dualizingComplexBaseChangeMap`, not a chosen isomorphism of its source and target. -/
noncomputable def sectionExceptionalComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' : Scheme.{u}} {d : ℕ} {P : ExceptionalSectionPair B d}
    {P' : ExceptionalSectionPair B' d} {v : B' ⟶ B}
    (e : ExceptionalSectionChange P P' v) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
        (sectionInvariant A P.map P.sect) ⟶ sectionInvariant A P'.map P'.sect :=
  (sectionCoherencePullbackIso A v P.sect P'.sect e.upper
      e.section_comm.symm (dualizingComplex (ModuleCat.{u + 1} A) P.map)).hom ≫
    (upperStar (ModuleCat.{u + 1} A) P'.sect).leftDerivedFunctor.map
      (dualizingComplexBaseChangeMap A e.square)

/-- The zero or one section of the affine line. Source: blueprint sk-thm-dnc, opening
fibre restrictions (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def exceptionalFamilyPoint (S : Scheme.{u}) (t : Bool) :
    S ⟶ AffineSpace (ULift.{u} (Fin 1)) S :=
  if t then AffineSpace.oneSection (ULift.{u} (Fin 1)) S
  else AffineSpace.zeroSection (ULift.{u} (Fin 1)) S

/-- A section family over the affine line with its two Cartesian fibre pairs.
Source: blueprint sk-thm-dnc, opening fibre restrictions
(blueprint: lem-trf-section-exceptional-fibre-coherence).
No isomorphism of derived objects is a field of this geometric record. -/
structure ExceptionalSectionFamily (S : Scheme.{u}) (d : ℕ) where
  ambient : ExceptionalSectionPair (AffineSpace (ULift.{u} (Fin 1)) S) d
  fibre : Bool → ExceptionalSectionPair S d
  restriction : ∀ t : Bool,
    ExceptionalSectionChange ambient (fibre t) (exceptionalFamilyPoint S t)

/-- The specified fibre map: `theta` at one and `eta` at zero. Source: blueprint sk-thm-dnc,
opening fibre restrictions (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def ExceptionalSectionFamily.fibreMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}} {d : ℕ} (P : ExceptionalSectionFamily S d) (t : Bool) :=
  sectionExceptionalComparison A (P.restriction t)

/-- A base-changed family and its Cartesian fibre diagram. The last equations express
that these are the induced maps of the fibres. Source: blueprint sk-thm-dnc, Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
structure ExceptionalFamilyBaseChange {S S' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionFamily S d) (P' : ExceptionalSectionFamily S' d) (v : S' ⟶ S) where
  ambient : ExceptionalSectionChange P.ambient P'.ambient
    (AffineSpace.map (ULift.{u} (Fin 1)) v)
  fibre : ∀ t : Bool, ExceptionalSectionChange (P.fibre t) (P'.fibre t) v
  point_comm : ∀ t : Bool, v ≫ exceptionalFamilyPoint S t =
    exceptionalFamilyPoint S' t ≫ AffineSpace.map (ULift.{u} (Fin 1)) v
  fibre_comm : ∀ t : Bool, (fibre t).upper ≫ (P.restriction t).upper =
    (P'.restriction t).upper ≫ ambient.upper

/-- The canonical counit-normalized locality isomorphism for a structural map and an etale
map into its source, evaluated at the constant unit. Source: blueprint sk-thm-dnc, Local
construction (blueprint: lem-trf-section-exceptional-fibre-coherence). The choice is from the
unique counit-normalized isomorphism of `lem-amb-etale-adjoint-locality`; hence its data are
determined, rather than chosen from an uncharacterized existence assertion. -/
noncomputable def sectionStructuralLocalityIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (h : U ⟶ X) [Etale h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (f : X ⟶ B) [HasCompactification f] (f' : U ⟶ B) [HasCompactification f']
    (hf : h ≫ f = f') :
    (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj
      (dualizingComplex (ModuleCat.{u + 1} A) f) ≅
        dualizingComplex (ModuleCat.{u + 1} A) f' := by
  subst f'
  exact (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).app _ ≪≫
    (Classical.choose (existsUnique_etaleAmbientAdjointLocalityIso A h f
      (HasCompactification.compactification f)
      (HasCompactification.compactification (h ≫ f))
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f)
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) (h ≫ f))
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (h ≫ f)))).app (𝟙_ _)

/-- An etale finite-type map of section pairs with Cartesian centres. Source: blueprint
sk-thm-dnc, Local construction (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
structure ExceptionalSectionEtaleMap {B : Scheme.{u}} {d : ℕ}
    (P P₁ : ExceptionalSectionPair B d) where
  upper : P₁.total ⟶ P.total
  map_comm : upper ≫ P.map = P₁.map
  section_comm : P₁.sect ≫ upper = P.sect
  centres : IsPullback (𝟙 B) P₁.sect P.sect upper
  [etale : Etale upper]
  [separated : IsSeparated upper]
  [finite_type : LocallyOfFiniteType upper]
  [quasi_compact : QuasiCompact upper]

attribute [instance] ExceptionalSectionEtaleMap.etale ExceptionalSectionEtaleMap.separated
  ExceptionalSectionEtaleMap.finite_type ExceptionalSectionEtaleMap.quasi_compact

/-- Section pullback of the counit-normalized etale locality isomorphism. Source: blueprint
sk-thm-dnc, Local construction (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def sectionExceptionalLocalityIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B : Scheme.{u}} {d : ℕ} {P P₁ : ExceptionalSectionPair B d}
    (h : ExceptionalSectionEtaleMap P P₁) :
    sectionInvariant A P.map P.sect ≅ sectionInvariant A P₁.map P₁.sect :=
  letI := P.base_noetherian
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) P₁.sect h.upper
      P.sect h.section_comm.symm).app _ ≪≫
    (upperStar (ModuleCat.{u + 1} A) P₁.sect).leftDerivedFunctor.mapIso
      (sectionStructuralLocalityIso A h.upper P.map P₁.map h.map_comm)

/-- An etale map of the whole family and its induced fibre maps. Source: blueprint
sk-thm-dnc, Local construction (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
structure ExceptionalFamilyEtaleMap {S : Scheme.{u}} {d : ℕ}
    (P P₁ : ExceptionalSectionFamily S d) where
  ambient : ExceptionalSectionEtaleMap P.ambient P₁.ambient
  fibre : ∀ t : Bool, ExceptionalSectionEtaleMap (P.fibre t) (P₁.fibre t)
  fibre_comm : ∀ t : Bool, (fibre t).upper ≫ (P.restriction t).upper =
    (P₁.restriction t).upper ≫ ambient.upper

/-- Normalization of a family isomorphism at the one fibre, including the inverse-image
unit compositor. Source: blueprint sk-thm-dnc, Local construction and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
def ExceptionalSectionFamily.IsNormalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}} {d : ℕ} (P : ExceptionalSectionFamily S d)
    (κ : sectionInvariant A P.ambient.map P.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P.fibre true).map (P.fibre true).sect)) : Prop :=
  (upperStar (ModuleCat.{u + 1} A) (exceptionalFamilyPoint S true)).leftDerivedFunctor.map
      κ.hom ≫
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
      (AffineSpace.oneSection_comp_over _ _)).hom.app _ = P.fibreMap A true

/-- The specialization determined by a normalized family isomorphism, from the one fibre
to the zero fibre. Source: blueprint sk-thm-dnc, final paragraph
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def ExceptionalSectionFamily.specialization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}} {d : ℕ} (P : ExceptionalSectionFamily S d)
    (κ : sectionInvariant A P.ambient.map P.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P.fibre true).map (P.fibre true).sect)) :
    sectionInvariant A (P.fibre true).map (P.fibre true).sect ⟶
      sectionInvariant A (P.fibre false).map (P.fibre false).sect :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.zeroSection_comp_over _ _)).inv.app _ ≫
  (upperStar (ModuleCat.{u + 1} A) (exceptionalFamilyPoint S false)).leftDerivedFunctor.map
    κ.inv ≫ P.fibreMap A false


private theorem normalized_transport
    {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) (H : D ⥤ C) (T : G ⋙ H ≅ 𝟭 C)
    {X X' : D} {Y Y' : C} (b : X ≅ X') (c : Y ≅ Y') (κ : X ≅ G.obj Y)
    (θ : H.obj X ⟶ Y) (θ' : H.obj X' ⟶ Y')
    (hk : H.map κ.hom ≫ T.hom.app Y = θ)
    (hs : H.map b.hom ≫ θ' = θ ≫ c.hom) :
    H.map (b.symm ≪≫ κ ≪≫ G.mapIso c).hom ≫ T.hom.app Y' = θ' := by
  have hn := T.hom.naturality c.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [hn, reassoc_of% hk, ← hs]
  rw [← H.map_comp_assoc, b.inv_hom_id, H.map_id, Category.id_comp]

private theorem specialization_transport
    {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) (H : D ⥤ C) (T : G ⋙ H ≅ 𝟭 C)
    {X X' : D} {Y Y' Z Z' : C} (b : X ≅ X') (c : Y ≅ Y')
    (κ : X ≅ G.obj Y) (κ' : X' ≅ G.obj Y')
    (θ : H.obj X ⟶ Z) (θ' : H.obj X' ⟶ Z') (z : Z ⟶ Z')
    (hk : b.hom ≫ κ'.hom = κ.hom ≫ G.map c.hom)
    (hs : H.map b.hom ≫ θ' = θ ≫ z) :
    c.hom ≫ T.inv.app Y' ≫ H.map κ'.inv ≫ θ' =
      (T.inv.app Y ≫ H.map κ.inv ≫ θ) ≫ z := by
  have hi : G.map c.hom ≫ κ'.inv = κ.inv ≫ b.hom := by
    rw [← cancel_epi κ.hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [← reassoc_of% hk]
    simp
  have hn := T.inv.naturality c.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, hi, Functor.map_comp,
    Category.assoc, hs]
  simp only [Category.assoc]

private theorem normalized_base_transport
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (G : C ⥤ D) (H : D ⥤ C) (G' : C' ⥤ D') (H' : D' ⥤ C')
    (U : C ⥤ C') (V : D ⥤ D') (T : G ⋙ H ≅ 𝟭 C) (T' : G' ⋙ H' ≅ 𝟭 C')
    (J : U ⋙ G' ≅ G ⋙ V) (L : H ⋙ U ≅ V ⋙ H')
    {X : D} {X' : D'} {Y : C} {Y' : C'}
    (b : V.obj X ≅ X') (c : U.obj Y ≅ Y') (κ : X ≅ G.obj Y)
    (θ : H.obj X ⟶ Y) (θ' : H'.obj X' ⟶ Y')
    (hk : H.map κ.hom ≫ T.hom.app Y = θ)
    (hs : L.hom.app X ≫ H'.map b.hom ≫ θ' = U.map θ ≫ c.hom)
    (hT : H'.map (J.inv.app Y) ≫ T'.hom.app (U.obj Y) =
      L.inv.app (G.obj Y) ≫ U.map (T.hom.app Y)) :
    H'.map (b.symm ≪≫ V.mapIso κ ≪≫ (J.app Y).symm ≪≫ G'.mapIso c).hom ≫
      T'.hom.app Y' = θ' := by
  have hn := T'.hom.naturality c.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hl := L.inv.naturality κ.hom
  simp only [Functor.comp_map] at hl
  apply (cancel_epi (L.hom.app X ≫ H'.map b.hom)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  rw [← H'.map_comp_assoc, b.hom_inv_id, H'.map_id, Category.id_comp,
    hn, reassoc_of% hT, reassoc_of% hl, Iso.hom_inv_id_app_assoc,
    ← U.map_comp_assoc, hk, hs]

private theorem specialization_base_transport
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (G : C ⥤ D) (H : D ⥤ C) (G' : C' ⥤ D') (H' : D' ⥤ C')
    (U : C ⥤ C') (V : D ⥤ D') (T : G ⋙ H ≅ 𝟭 C) (T' : G' ⋙ H' ≅ 𝟭 C')
    (J : U ⋙ G' ≅ G ⋙ V) (L : H ⋙ U ≅ V ⋙ H')
    {X : D} {X' : D'} {Y Z : C} {Y' Z' : C'}
    (b : V.obj X ≅ X') (c : U.obj Y ≅ Y') (κ : X ≅ G.obj Y)
    (κ' : X' ≅ G'.obj Y') (θ : H.obj X ⟶ Z) (θ' : H'.obj X' ⟶ Z')
    (z : U.obj Z ⟶ Z')
    (hk : b.hom ≫ κ'.hom = V.map κ.hom ≫ J.inv.app Y ≫ G'.map c.hom)
    (hs : L.hom.app X ≫ H'.map b.hom ≫ θ' = U.map θ ≫ z)
    (hT : H'.map (J.inv.app Y) ≫ T'.hom.app (U.obj Y) =
      L.inv.app (G.obj Y) ≫ U.map (T.hom.app Y)) :
    c.hom ≫ T'.inv.app Y' ≫ H'.map κ'.inv ≫ θ' =
      U.map (T.inv.app Y ≫ H.map κ.inv ≫ θ) ≫ z := by
  have hi : G'.map c.hom ≫ κ'.inv = J.hom.app Y ≫ V.map κ.inv ≫ b.hom := by
    apply (cancel_epi (V.map κ.hom ≫ J.inv.app Y)).mp
    simp only [Category.assoc]
    rw [← reassoc_of% hk, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_app_assoc,
      ← V.map_comp_assoc, κ.hom_inv_id, V.map_id, Category.id_comp]
  have ht : T'.inv.app (U.obj Y) ≫ H'.map (J.hom.app Y) =
      U.map (T.inv.app Y) ≫ L.hom.app (G.obj Y) := by
    have hh : (H'.mapIso (J.symm.app Y) ≪≫ T'.app (U.obj Y)) =
        (L.symm.app (G.obj Y) ≪≫ U.mapIso (T.app Y)) := Iso.ext hT
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv]
      using congrArg Iso.inv hh
  have hn := T'.inv.naturality c.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hl := L.hom.naturality κ.inv
  simp only [Functor.comp_map] at hl
  rw [reassoc_of% hn, ← H'.map_comp_assoc, hi, H'.map_comp, H'.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% ht, ← reassoc_of% hl, hs]
  simp only [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem locality_inverse_counit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} {F : D ⥤ E} {G : E ⥤ D}
    {T : C ⥤ E} {H : E ⥤ C}
    (a : L ⊣ R) (b : F ⊣ G) (c : T ⊣ H)
    (α : L ⋙ F ≅ T) (ℓ : G ⋙ R ≅ H)
    (hℓ : ∀ K, T.map (ℓ.hom.app K) ≫ c.counit.app K =
      α.inv.app _ ≫ F.map (a.counit.app (G.obj K)) ≫ b.counit.app K) (K : E) :
    F.map (L.map (ℓ.inv.app K)) ≫ F.map (a.counit.app (G.obj K)) ≫
      b.counit.app K = α.hom.app _ ≫ c.counit.app K := by
  apply (cancel_epi (α.inv.app (H.obj K))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% (α.inv.naturality (ℓ.inv.app K)), ← hℓ]
  simp only [← T.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem locality_mate_naturality
    {C D E C' D' E' : Type*}
    [Category* C] [Category* D] [Category* E]
    [Category* C'] [Category* D'] [Category* E']
    {L : C ⥤ D} {R : D ⥤ C} {F : D ⥤ E} {G : E ⥤ D}
    {T : C ⥤ E} {H : E ⥤ C}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {F' : D' ⥤ E'} {G' : E' ⥤ D'}
    {T' : C' ⥤ E'} {H' : E' ⥤ C'}
    (a : L ⊣ R) (b : F ⊣ G) (c : T ⊣ H)
    (a' : L' ⊣ R') (b' : F' ⊣ G') (c' : T' ⊣ H')
    {U : C ⥤ C'} {V : D ⥤ D'} {W : E ⥤ E'}
    (α : L ⋙ F ≅ T) (α' : L' ⋙ F' ≅ T')
    (ℓ : G ⋙ R ≅ H) (ℓ' : G' ⋙ R' ≅ H')
    (hℓ : ∀ K, T.map (ℓ.hom.app K) ≫ c.counit.app K =
      α.inv.app _ ≫ F.map (a.counit.app (G.obj K)) ≫ b.counit.app K)
    (hℓ' : ∀ K, T'.map (ℓ'.hom.app K) ≫ c'.counit.app K =
      α'.inv.app _ ≫ F'.map (a'.counit.app (G'.obj K)) ≫ b'.counit.app K)
    (J : R ⋙ U ⟶ V ⋙ R')
    (ξ : TwoSquare V F F' W) (ζ : TwoSquare U T T' W)
    (hx : ∀ M, ζ.app M ≫ W.map (α.inv.app M) =
      α'.inv.app (U.obj M) ≫
        F'.map (((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ J)).app M) ≫
          ξ.app (L.obj M)) (K : E) :
    J.app (G.obj K) ≫ R'.map ((mateEquiv b b' ξ).app K) ≫
      ℓ'.hom.app (W.obj K) = U.map (ℓ.hom.app K) ≫ (mateEquiv c c' ζ).app K := by
  have hm := Adjunction.mateEquiv_inv_comp a b c a' b' c'
    ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ J)) ξ ζ α.symm α'.symm hx
    ℓ.inv (locality_inverse_counit a b c α ℓ hℓ)
    ℓ'.inv (locality_inverse_counit a' b' c' α' ℓ' hℓ') K
  simp only [Equiv.apply_symm_apply, TwoSquare.mk, TwoSquare.natTrans] at hm
  apply (cancel_epi (U.map (ℓ.inv.app K))).mp
  simp only [← U.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hm]
  simp

private theorem section_comparison_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' : Scheme.{u}} {d : ℕ} (P : ExceptionalSectionPair B d)
    (P' : ExceptionalSectionPair B' d) (v : B' ⟶ B)
    [HasInvertibleExponent A P.total] (e : ExceptionalSectionChange P P' v) :
    IsIso (sectionExceptionalComparison A e) := by
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    A P.map d e.square
  have : IsIso (dualizingComplexBaseChangeMap A e.square) := by
    unfold dualizingComplexBaseChangeMap
    infer_instance
  unfold sectionExceptionalComparison
  infer_instance

private theorem exceptional_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (K : DerivedCategoryModule A Y) :
    (rightDerivedUpperShriekBaseChangeMap A (sq₂.paste_horiz sq₁)).app K =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        ((rightDerivedUpperShriekBaseChangeMap A sq₁).app K) ≫
      (rightDerivedUpperShriekBaseChangeMap A sq₂).app
        ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K) ≫
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f'').map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).inv.app K) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₁
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₂
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)
  let E₁ := rightDerivedLowerShriekBaseChangeMap A sq₁
  let E₂ := rightDerivedLowerShriekBaseChangeMap A sq₂
  let E₃ := rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v
  let c' := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v'
  let δ₁ := TwoSquare.mk _ _ _ _ (inv E₁)
  let δ₂ := TwoSquare.mk _ _ _ _ (inv E₂)
  have h : TwoSquare.mk _ _ _ _ (inv E₃) =
      ((δ₁.hComp δ₂).whiskerTop c'.hom).whiskerBottom c.inv := by
    apply TwoSquare.ext
    intro M
    dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    let Vw := (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor
    let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f''
    have he : (asIso E₃).app M =
        c.app _ ≪≫ Vw.mapIso ((asIso E₁).app M) ≪≫
          (asIso E₂).app _ ≪≫ F.mapIso (c'.symm.app M) := by
      apply Iso.ext
      apply (cancel_epi (c.inv.app _)).mp
      apply (cancel_mono (F.map (c'.hom.app M))).mp
      simp only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        asIso_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
        ← F.map_comp, Iso.inv_hom_id_app]
      have hid := CategoryTheory.Functor.map_id F
        (((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctor ⋙
          (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor).obj M)
      rw [hid]
      erw [Category.comp_id]
      exact (affineLinearExchange_paste A sq₁ sq₂ M).symm
    have hi := congrArg Iso.inv he
    simpa only [Iso.app_inv, asIso_inv, Iso.trans_inv, Functor.mapIso_inv,
      Iso.symm_inv, Category.assoc, Vw, F] using hi
  have hm := congrArg (fun z ↦ z.natTrans.app K)
    (congrArg (mateEquiv
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f'')) h)
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp] at hm
  simpa only [rightDerivedUpperShriekBaseChangeMap, δ₁, δ₂, E₁, E₂, E₃,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.natTrans, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, c, c'] using hm

private theorem dualizing_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w) :
    dualizingComplexBaseChangeMap A (sq₂.paste_horiz sq₁) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app
        (dualizingComplex (ModuleCat.{u + 1} A) f) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A sq₁) ≫ dualizingComplexBaseChangeMap A sq₂ := by
  have hu := (canonicalDerivedPullbackCompositionMonoidal A v w (𝟙 Y'')
    (𝟙_ _) (𝟙_ _)).2.1
  have hn := (rightDerivedUpperShriekBaseChangeMap A sq₂).naturality
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v).hom
  simp only [Functor.comp_map] at hn
  unfold dualizingComplexBaseChangeMap dualizingComplex
  rw [exceptional_base_comp A sq₁ sq₂]
  simp only [Category.assoc, Functor.map_comp]
  erw [reassoc_of% hn]
  rw [← hu]
  simp only [Functor.map_comp]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]


private theorem section_pullback_comp
    (A : Type (u + 1)) [CommRing A]
    {B B' B'' X X' X'' : Scheme.{u}}
    (v : B' ⟶ B) (w : B'' ⟶ B')
    (s : B ⟶ X) (s' : B' ⟶ X') (s'' : B'' ⟶ X'')
    (r : X' ⟶ X) (r' : X'' ⟶ X')
    (h₁ : v ≫ s = s' ≫ r) (h₂ : w ≫ s' = s'' ≫ r')
    (h₃ : (w ≫ v) ≫ s = s'' ≫ (r' ≫ r)) (K : DerivedCategoryModule A X) :
    (sectionCoherencePullbackIso A (w ≫ v) s s'' (r' ≫ r) h₃ K).hom ≫
        (upperStar (ModuleCat.{u + 1} A) s'').leftDerivedFunctor.map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r' r).hom.app K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).hom.app
        ((upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor.map
        (sectionCoherencePullbackIso A v s s' r h₁ K).hom ≫
      (sectionCoherencePullbackIso A w s' s'' r' h₂
        ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K)).hom := by
  let C := ModuleCat.{u + 1} A
  have ha := leftDerivedUpperStarComp_assoc'_app C w v s (w ≫ v) (v ≫ s)
    ((w ≫ v) ≫ s) rfl rfl rfl K
  have hb := leftDerivedUpperStarComp_assoc'_app C w s' r (w ≫ s') (v ≫ s)
    ((w ≫ v) ≫ s) rfl h₁ (by rw [Category.assoc, h₁, Category.assoc]) K
  have hc := leftDerivedUpperStarComp_assoc'_app C s'' r' r (w ≫ s') (r' ≫ r)
    ((w ≫ v) ≫ s) h₂ rfl (by rw [Category.assoc, h₁, Category.assoc]) K
  unfold sectionCoherencePullbackIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  apply (cancel_epi ((leftDerivedUpperStarComp C (w ≫ v) s).hom.app K)).mp
  dsimp only [C] at ha hb hc ⊢
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% ha]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [reassoc_of% hb, Iso.hom_inv_id_app_assoc]
  exact hc

/-- Transitivity of the structural section comparison for successive changes of base.
Source: blueprint sk-thm-dnc, Gluing; Stacks 0F7L, compatibility with composite base changes
(blueprint: lem-trf-section-exceptional-fibre-coherence).
Proof: paste inverse compact-support exchange squares, and apply mate-pasting to their
adjunctions. Both sides transpose to the pulled-back structural counit through the same
inverse exchange. Evaluate at the unit, use unit-composition coherence, and pull back by
the compatible final section. The displayed compositor inserts the canonical identification
of the iterated inverse image. This applies to each of q, g and pi in the section family.
-/
theorem sectionExceptional_comparison_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' B'' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionPair B d) (P' : ExceptionalSectionPair B' d)
    (P'' : ExceptionalSectionPair B'' d)
    (hInvertible : ∀ b : B, IsUnit (N : B.presheaf.stalk b))
    (v : B' ⟶ B) (w : B'' ⟶ B')
    (e : ExceptionalSectionChange P P' v) (e' : ExceptionalSectionChange P' P'' w)
    (e'' : ExceptionalSectionChange P P'' (w ≫ v))
    (hUpper : e''.upper = e'.upper ≫ e.upper) :
    sectionExceptionalComparison A e'' =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).hom.app
        (sectionInvariant A P.map P.sect) ≫
      (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor.map
        (sectionExceptionalComparison A e) ≫ sectionExceptionalComparison A e' := by
  have _ := hN
  have _ := hA
  have _ := hInvertible
  have := P.base_noetherian
  have := P'.base_noetherian
  have := P''.base_noetherian
  let E : ExceptionalSectionChange P P'' (w ≫ v) :=
    { upper := e'.upper ≫ e.upper
      square := e'.square.paste_horiz e.square
      section_comm := by rw [← Category.assoc, e'.section_comm,
        Category.assoc, e.section_comm, ← Category.assoc] }
  have he : e'' = E := by
    cases e'' with
    | mk upper square comm =>
      dsimp only at hUpper
      cases hUpper
      rfl
  rw [he]
  have hd := dualizing_base_comp A e.square e'.square
  have hp := section_pullback_comp A v w P.sect P'.sect P''.sect
    e.upper e'.upper e.section_comm.symm e'.section_comm.symm E.section_comm.symm
    (dualizingComplex (ModuleCat.{u + 1} A) P.map)
  unfold sectionExceptionalComparison sectionInvariant
  dsimp only [E]
  rw [hd]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hp]
  have hn := ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w P'.sect).symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{u + 1} A) P''.sect e'.upper
      (w ≫ P'.sect) e'.section_comm.symm).hom.naturality
      (dualizingComplexBaseChangeMap A e.square)
  simp only [Functor.comp_map] at hn
  change _ = _ at hn
  erw [← reassoc_of% hn]
  rfl


private theorem section_comparison_comp_at
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' B'' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionPair B d) (P' : ExceptionalSectionPair B' d)
    (P'' : ExceptionalSectionPair B'' d)
    (hInvertible : ∀ b : B, IsUnit (N : B.presheaf.stalk b))
    (v : B' ⟶ B) (w : B'' ⟶ B') (z : B'' ⟶ B) (hz : z = w ≫ v)
    (e : ExceptionalSectionChange P P' v) (e' : ExceptionalSectionChange P' P'' w)
    (e'' : ExceptionalSectionChange P P'' z)
    (hUpper : e''.upper = e'.upper ≫ e.upper) :
    sectionExceptionalComparison A e'' =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v z hz).hom.app
        (sectionInvariant A P.map P.sect) ≫
      (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor.map
        (sectionExceptionalComparison A e) ≫ sectionExceptionalComparison A e' := by
  subst z
  exact sectionExceptional_comparison_comp A N hN hA P P' P'' hInvertible
    v w e e' e'' hUpper

/-- The specified base-change maps are invertible, and the two fibre squares commute.
Source: blueprint sk-thm-dnc, opening fibre restrictions and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence).
Proof: (1) write the exceptional comparison as the transpose of inverse compact-support
exchange followed by the pulled-back counit. Smooth exceptional base change makes it
invertible, including at the constant unit. (2) Compact-support pasting and mate pasting give
transitivity, with the canonical inverse-image and unit compositors. (3) The paths through
the old fibre and through the new affine line are the two factorizations of the same outer
Cartesian rectangle. Transitivity identifies their exceptional comparisons. Pull back by the
new fibre section, using its compatibility with the other sections. At true this is the theta
square, and at false it is the eta square. This is equality of the prescribed maps.
-/
theorem sectionExceptional_fibre_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S S' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionFamily S d) (P' : ExceptionalSectionFamily S' d)
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (v : S' ⟶ S) (e : ExceptionalFamilyBaseChange P P' v) :
    IsIso (sectionExceptionalComparison A e.ambient) ∧
    ∀ t : Bool,
      IsIso (P.fibreMap A t) ∧ IsIso (P'.fibreMap A t) ∧
      IsIso (sectionExceptionalComparison A (e.fibre t)) ∧
      (sectionCoherencePullbackIso A v (exceptionalFamilyPoint S t)
        (exceptionalFamilyPoint S' t) (AffineSpace.map (ULift.{u} (Fin 1)) v)
        (e.point_comm t) (sectionInvariant A P.ambient.map P.ambient.sect)).hom ≫
          (upperStar (ModuleCat.{u + 1} A) (exceptionalFamilyPoint S' t)).leftDerivedFunctor.map
            (sectionExceptionalComparison A e.ambient) ≫ P'.fibreMap A t =
        (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map (P.fibreMap A t) ≫
          sectionExceptionalComparison A (e.fibre t) := by
  have hNS : IsUnit (N : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using hInvertible x
  have : HasInvertibleExponent A S := ⟨N, hN, hA, hNS⟩
  have : HasInvertibleExponent A P.ambient.total :=
    .of_hom (P.ambient.map ≫ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
  have : HasInvertibleExponent A P'.ambient.total :=
    .of_hom (P'.ambient.map ≫ (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') ≫ v)
  have ha : IsIso (sectionExceptionalComparison A e.ambient) :=
    section_comparison_isIso A _ _ _ e.ambient
  refine ⟨ha, fun t ↦ ?_⟩
  have : HasInvertibleExponent A (P.fibre t).total := .of_hom (P.fibre t).map
  refine ⟨section_comparison_isIso A _ _ _ (P.restriction t),
    section_comparison_isIso A _ _ _ (P'.restriction t),
    section_comparison_isIso A _ _ _ (e.fibre t), ?_⟩
  let E : ExceptionalSectionChange P.ambient (P'.fibre t)
      (v ≫ exceptionalFamilyPoint S t) :=
    { upper := (e.fibre t).upper ≫ (P.restriction t).upper
      square := (e.fibre t).square.paste_horiz (P.restriction t).square
      section_comm := by rw [← Category.assoc, (e.fibre t).section_comm,
        Category.assoc, (P.restriction t).section_comm, ← Category.assoc] }
  have hL : ∀ x : AffineSpace (ULift.{u} (Fin 1)) S,
      IsUnit (N : (AffineSpace (ULift.{u} (Fin 1)) S).presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using
      (hNS.map (AffineSpace (ULift.{u} (Fin 1)) S ↘ S).appTop.hom).map
        (((AffineSpace (ULift.{u} (Fin 1)) S).presheaf.germ ⊤ x trivial).hom)
  have h₁ := section_comparison_comp_at A N hN hA P.ambient (P.fibre t)
    (P'.fibre t) hL (exceptionalFamilyPoint S t) v _ rfl
    (P.restriction t) (e.fibre t) E rfl
  have h₂ := section_comparison_comp_at A N hN hA P.ambient P'.ambient
    (P'.fibre t) hL (AffineSpace.map (ULift.{u} (Fin 1)) v)
    (exceptionalFamilyPoint S' t) _ (e.point_comm t) e.ambient
    (P'.restriction t) E (e.fibre_comm t)
  unfold sectionCoherencePullbackIso ExceptionalSectionFamily.fibreMap
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  rw [← h₂, h₁, Iso.inv_hom_id_app_assoc]


private noncomputable def structural_locality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (u : U ⟶ X) [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (f : X ⟶ B) [HasCompactification f] [HasCompactification (u ≫ f)] :
    rightDerivedUpperShriek (ModuleCat.{u + 1} A) f ⋙
        (upperStar (ModuleCat.{u + 1} A) u).leftDerivedFunctor ≅
      rightDerivedUpperShriek (ModuleCat.{u + 1} A) (u ≫ f) :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) u) ≪≫
  Classical.choose (existsUnique_etaleAmbientAdjointLocalityIso A u f
    (HasCompactification.compactification f)
    (HasCompactification.compactification (u ≫ f))
    (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedUpperShriek (ModuleCat.{u + 1} A) (u ≫ f))
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (u ≫ f)))

set_option backward.isDefEq.respectTransparency false in
private theorem structural_locality_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (u : U ⟶ X) [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (f : X ⟶ B) [HasCompactification f] [HasCompactification (u ≫ f)]
    (K : DerivedCategoryModule A B) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (u ≫ f)).map
        ((structural_locality A u f).hom.app K) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (u ≫ f)).counit.app K =
      (etaleAmbientLeftComparison A N u f
        (HasCompactification.compactification f)
        (HasCompactification.compactification (u ≫ f))).inv.app _ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) u inferInstance).ofNatIsoRight
            (leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) u).symm).counit.app
                ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K)) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app K := by
  have hh := (Classical.choose_spec (existsUnique_etaleAmbientAdjointLocalityIso A u f
    (HasCompactification.compactification f)
    (HasCompactification.compactification (u ≫ f))
    (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedUpperShriek (ModuleCat.{u + 1} A) (u ≫ f))
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (u ≫ f)))).1 N K
  simp only [structural_locality, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  change (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (u ≫ f)).map _ ≫ _ = _ at hh
  rw [hh]
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.symm_inv, Functor.map_comp, Category.assoc]
  have hn := (etaleAmbientLeftComparison A N u f
    (HasCompactification.compactification f)
    (HasCompactification.compactification (u ≫ f))).inv.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) u).hom.app
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K))
  change (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (u ≫ f)).map _ ≫ _ =
    _ ≫ (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map _ at hn
  rw [reassoc_of% hn]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem structural_locality_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X B U' X' B' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    [IsNoetherian U'] [IsNoetherian X'] [IsNoetherian B']
    (u : U ⟶ X) (f : X ⟶ B) (u' : U' ⟶ X') (f' : X' ⟶ B')
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [Etale u'] [IsSeparated u'] [LocallyOfFiniteType u'] [QuasiCompact u']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f']
    (f₁ : U ⟶ B) (hf₁ : u ≫ f = f₁)
    (f₁' : U' ⟶ B') (hf₁' : u' ≫ f' = f₁')
    [HasCompactification f₁] [HasCompactification f₁']
    [QuasiCompact f'] [QuasiCompact f₁']
    (v : B' ⟶ B) (r : X' ⟶ X) (r₁ : U' ⟶ U)
    (sq : IsPullback r f' f v) (sqU : IsPullback r₁ u' u r)
    (sq₁ : IsPullback r₁ f₁' f₁ v) :
    (sectionCoherencePullbackIso A r₁ u u' r sqU.w
      (dualizingComplex (ModuleCat.{u + 1} A) f)).hom ≫
      (upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A sq) ≫
      (sectionStructuralLocalityIso A u' f' f₁' hf₁').hom =
      (upperStar (ModuleCat.{u + 1} A) r₁).leftDerivedFunctor.map
        (sectionStructuralLocalityIso A u f f₁ hf₁).hom ≫
      dualizingComplexBaseChangeMap A sq₁ := by
  subst f₁
  subst f₁'
  obtain ⟨N⟩ := nonempty_etaleCompactSupportNormalization A
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₁
  let C := ModuleCat.{u + 1} A
  let a := (derivedEtaleLowerShriekUpperStarAdjunction C u inferInstance).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory C u).symm
  let a' := (derivedEtaleLowerShriekUpperStarAdjunction C u' inferInstance).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory C u').symm
  let α := etaleAmbientLeftComparison A N u f
    (HasCompactification.compactification f)
    (HasCompactification.compactification (u ≫ f))
  let α' := etaleAmbientLeftComparison A N u' f'
    (HasCompactification.compactification f')
    (HasCompactification.compactification (u' ≫ f'))
  let J := (leftDerivedUpperStarComp C r₁ u).symm ≪≫
    leftDerivedUpperStarComp C u' r (r₁ ≫ u) sqU.w
  have hm := locality_mate_naturality a
    (rightDerivedUpperShriekAdjunction C f)
    (rightDerivedUpperShriekAdjunction C (u ≫ f)) a'
    (rightDerivedUpperShriekAdjunction C f')
    (rightDerivedUpperShriekAdjunction C (u' ≫ f'))
    α α' (structural_locality A u f) (structural_locality A u' f')
    (structural_locality_counit A N u f) (structural_locality_counit A N u' f')
    J.hom (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap A sq)))
    (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap A sq₁)))
    (etaleAmbientLeftComparison_baseChange A N u f u' f' v r r₁ sq sqU sq₁) (𝟙_ _)
  have hn := (structural_locality A u' f').hom.naturality
    (leftDerivedUpperStarUnitIso C v).hom
  simp only [Functor.comp_map] at hn
  have ht := congrArg (fun z ↦ z ≫
    (rightDerivedUpperShriek C (u' ≫ f')).map
      (leftDerivedUpperStarUnitIso C v).hom) hm
  dsimp only [TwoSquare.mk, TwoSquare.natTrans] at ht
  change _ = _ at ht
  simp only [Category.assoc] at ht
  rw [← hn] at ht
  simpa only [dualizingComplexBaseChangeMap, sectionStructuralLocalityIso,
    structural_locality, sectionCoherencePullbackIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc,
    rightDerivedUpperShriekBaseChangeMap, dualizingComplex, C, J] using ht

private theorem section_pullback_locality_comp
    (A : Type (u + 1)) [CommRing A]
    {B B' X X' Y Y' : Scheme.{u}}
    (v : B' ⟶ B) (s : B ⟶ X) (s' : B' ⟶ X')
    (s₁ : B ⟶ Y) (s₁' : B' ⟶ Y')
    (u : Y ⟶ X) (u' : Y' ⟶ X') (r : X' ⟶ X) (r₁ : Y' ⟶ Y)
    (hs : v ≫ s = s' ≫ r) (hs₁ : v ≫ s₁ = s₁' ≫ r₁)
    (hu : s₁ ≫ u = s) (hu' : s₁' ≫ u' = s')
    (hr : r₁ ≫ u = u' ≫ r) (K : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s₁ u s hu.symm).hom.app K) ≫
      (sectionCoherencePullbackIso A v s₁ s₁' r₁ hs₁
        ((upperStar (ModuleCat.{u + 1} A) u).leftDerivedFunctor.obj K)).hom ≫
      (upperStar (ModuleCat.{u + 1} A) s₁').leftDerivedFunctor.map
        (sectionCoherencePullbackIso A r₁ u u' r hr K).hom =
    (sectionCoherencePullbackIso A v s s' r hs K).hom ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s₁' u' s' hu'.symm).hom.app
        ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K) := by
  let C := ModuleCat.{u + 1} A
  have ha := leftDerivedUpperStarComp_assoc'_app C v s₁ u (v ≫ s₁) s (v ≫ s)
    rfl hu.symm (by rw [Category.assoc, hu]) K
  have hb := leftDerivedUpperStarComp_assoc'_app C s₁' r₁ u (v ≫ s₁)
    (r₁ ≫ u) (v ≫ s) hs₁ rfl (by rw [Category.assoc, hu]) K
  have hc := leftDerivedUpperStarComp_assoc'_app C s₁' u' r s' (r₁ ≫ u) (v ≫ s)
    hu'.symm hr hs K
  dsimp only [C] at ha hb hc ⊢
  unfold sectionCoherencePullbackIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v s).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% ha, Iso.hom_inv_id_app_assoc, ← reassoc_of% hb]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact hc

/-- Counit-normalized etale locality commutes with both exceptional fibre comparisons.
Source: blueprint sk-thm-dnc, Local construction and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence).
Proof: (4) etale locality is the right-adjoint conjugate of compact-support composition;
its transpose is the inverse composition comparison followed by the sum-extension evaluation
and the structural counit. (5) The specified etale sum-extension base-change comparison
preserves evaluation: compare transposes under the composite adjunction, expand underived
exchange, and use naturality and the triangle identities. This equality descends degreewise
to the unbounded categories. (6) Transpose locality followed by exceptional base change in
both orders. Compact-support composition/base-change compatibility, step (5), and the mate
pasting rules give the same transpose. (7) Apply this to q and each fibre inclusion, evaluate
at the unit and pull back by the sections. The resulting equalities are precisely the two
squares below, for the actual counit-normalized locality maps.
-/
theorem sectionExceptional_etale_fibre_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S : Scheme.{u}} {d : ℕ}
    (P P₁ : ExceptionalSectionFamily S d)
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (h : ExceptionalFamilyEtaleMap P P₁) :
    ∀ t : Bool,
      (upperStar (ModuleCat.{u + 1} A) (exceptionalFamilyPoint S t)).leftDerivedFunctor.map
          (sectionExceptionalLocalityIso A h.ambient).hom ≫ P₁.fibreMap A t =
        P.fibreMap A t ≫ (sectionExceptionalLocalityIso A (h.fibre t)).hom := by
  have _ := hN
  have _ := hA
  have _ := hInvertible
  have := P.ambient.base_noetherian
  have := (P.fibre false).base_noetherian
  intro t
  have squ : IsPullback (P₁.restriction t).upper (h.fibre t).upper
      h.ambient.upper (P.restriction t).upper := by
    have ho := (P₁.restriction t).square
    rw [← h.ambient.map_comm, ← (h.fibre t).map_comm] at ho
    exact ho.of_bot (h.fibre_comm t).symm (P.restriction t).square
  have hd := structural_locality_baseChange A h.ambient.upper P.ambient.map
    (h.fibre t).upper (P.fibre t).map P₁.ambient.map h.ambient.map_comm
    (P₁.fibre t).map (h.fibre t).map_comm
    (exceptionalFamilyPoint S t) (P.restriction t).upper (P₁.restriction t).upper
    (P.restriction t).square squ (P₁.restriction t).square
  have hc := section_pullback_locality_comp A (exceptionalFamilyPoint S t)
    P.ambient.sect (P.fibre t).sect P₁.ambient.sect (P₁.fibre t).sect
    h.ambient.upper (h.fibre t).upper (P.restriction t).upper
    (P₁.restriction t).upper (P.restriction t).section_comm.symm
    (P₁.restriction t).section_comm.symm h.ambient.section_comm
    (h.fibre t).section_comm squ.w
    (dualizingComplex (ModuleCat.{u + 1} A) P.ambient.map)
  have hn := ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (exceptionalFamilyPoint S t) P₁.ambient.sect).symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (P₁.fibre t).sect
      (P₁.restriction t).upper (exceptionalFamilyPoint S t ≫ P₁.ambient.sect)
      (P₁.restriction t).section_comm.symm).hom.naturality
    (sectionStructuralLocalityIso A h.ambient.upper P.ambient.map P₁.ambient.map
      h.ambient.map_comm).hom
  simp only [Functor.comp_map] at hn
  unfold ExceptionalSectionFamily.fibreMap sectionExceptionalComparison
    sectionExceptionalLocalityIso sectionInvariant
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  rw [← CategoryTheory.Functor.map_comp, ← hd]
  simp only [Functor.map_comp]
  erw [reassoc_of% hc]
  have hn' := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (P₁.fibre t).sect
    (h.fibre t).upper (P.fibre t).sect (h.fibre t).section_comm.symm).hom.naturality
    (dualizingComplexBaseChangeMap A (P.restriction t).square)
  simp only [Functor.comp_map] at hn'
  erw [← reassoc_of% hn']

/-- Uniquely normalized family isomorphisms, and their specializations, respect the actual
exceptional base-change maps. Source: blueprint sk-thm-dnc, Gluing and final restriction
(blueprint: lem-trf-section-exceptional-fibre-coherence).
Proof: (8) transport kappa by the invertible ambient comparison and the pulled-back one-fibre
comparison. The fibre square above and inverse-image composition show that this transported
isomorphism is normalized by theta prime. Uniqueness identifies it with kappa prime.
(9) Restrict that equality to zero, invert its isomorphism part, and compose with eta prime.
The zero-fibre square cancels the ambient comparison and gives the specialization square.
The first equation below is the kappa formula multiplied by b_F on the source; invertibility
of b_F, supplied by sectionExceptional_fibre_coherence, gives exactly the formula with b_F⁻¹.
-/
theorem sectionExceptional_normalized_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S S' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionFamily S d) (P' : ExceptionalSectionFamily S' d)
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (v : S' ⟶ S) (e : ExceptionalFamilyBaseChange P P' v)
    (κ : sectionInvariant A P.ambient.map P.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P.fibre true).map (P.fibre true).sect))
    (κ' : sectionInvariant A P'.ambient.map P'.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.obj
          (sectionInvariant A (P'.fibre true).map (P'.fibre true).sect))
    (hκ : P.IsNormalized A κ ∧ ∀ τ, P.IsNormalized A τ → τ = κ)
    (hκ' : P'.IsNormalized A κ' ∧ ∀ τ, P'.IsNormalized A τ → τ = κ') :
    sectionExceptionalComparison A e.ambient ≫ κ'.hom =
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) v)).leftDerivedFunctor.map κ.hom ≫
      (sectionCoherencePullbackIso A
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') v
        (AffineSpace.map (ULift.{u} (Fin 1)) v)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
        (AffineSpace.map_over v).symm
        (sectionInvariant A (P.fibre true).map (P.fibre true).sect)).inv ≫
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.map
          (sectionExceptionalComparison A (e.fibre true)) ∧
    sectionExceptionalComparison A (e.fibre true) ≫ P'.specialization A κ' =
      (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map (P.specialization A κ) ≫
        sectionExceptionalComparison A (e.fibre false) := by
  have hb := sectionExceptional_fibre_coherence A N hN hA P P' hInvertible v e
  have := hb.1
  have := (hb.2 true).2.2.1
  let U := (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor
  let V := (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace.map (ULift.{u} (Fin 1)) v)).leftDerivedFunctor
  let G := (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor
  let G' := (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor
  let C := sectionInvariant A (P.fibre true).map (P.fibre true).sect
  let b := asIso (sectionExceptionalComparison A e.ambient)
  let c := asIso (sectionExceptionalComparison A (e.fibre true))
  let J := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') v).symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (AffineSpace.map (ULift.{u} (Fin 1)) v)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
      ((AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') ≫ v) (AffineSpace.map_over v).symm
  let j := J.app C
  let τ := b.symm ≪≫ V.mapIso κ ≪≫ j.symm ≪≫ G'.mapIso c
  have hT (t : Bool) :
      (upperStar (ModuleCat.{u + 1} A)
        (exceptionalFamilyPoint S' t)).leftDerivedFunctor.map j.inv ≫
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
          (exceptionalFamilyPoint S' t)
          (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')
          (by cases t
              · exact AffineSpace.zeroSection_comp_over _ _
              · exact AffineSpace.oneSection_comp_over _ _)).hom.app (U.obj C) =
      (sectionCoherencePullbackIso A v (exceptionalFamilyPoint S t)
        (exceptionalFamilyPoint S' t) (AffineSpace.map (ULift.{u} (Fin 1)) v)
        (e.point_comm t) (G.obj C)).inv ≫
        U.map ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
          (exceptionalFamilyPoint S t)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
          (by cases t
              · exact AffineSpace.zeroSection_comp_over _ _
              · exact AffineSpace.oneSection_comp_over _ _)).hom.app C) := by
    have h₁ := congrArg Iso.inv (sectionPullback_endpoint A
      (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') v
      (AffineSpace.map (ULift.{u} (Fin 1)) v)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
      _ _ rfl (AffineSpace.map_over v).symm (AffineSpace.map_over v) rfl C)
    have h₂ := congrArg Iso.inv (sectionPullback_endpoint A v
      (exceptionalFamilyPoint S t) (exceptionalFamilyPoint S' t)
      (AffineSpace.map (ULift.{u} (Fin 1)) v)
      _ _ rfl (e.point_comm t) (e.point_comm t).symm rfl (G.obj C))
    dsimp only [Iso.app_inv, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app] at h₁ h₂
    change _ = _ at h₁ h₂
    dsimp only [sectionCoherencePullbackIso, j, J, Iso.trans_inv, Iso.symm_inv,
      Iso.app_inv, NatTrans.comp_app]
    rw [h₁, h₂]
    exact leftDerivedUpperStar_map_comp_compSectionIso (ModuleCat.{u + 1} A) v
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
      (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')
      (AffineSpace.map (ULift.{u} (Fin 1)) v)
      (exceptionalFamilyPoint S t) (exceptionalFamilyPoint S' t)
      (AffineSpace.map_over v) (e.point_comm t).symm _ _ C
  let H (t : Bool) := (upperStar (ModuleCat.{u + 1} A)
    (exceptionalFamilyPoint S t)).leftDerivedFunctor
  let H' (t : Bool) := (upperStar (ModuleCat.{u + 1} A)
    (exceptionalFamilyPoint S' t)).leftDerivedFunctor
  let T (t : Bool) : G ⋙ H t ≅ 𝟭 _ := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (exceptionalFamilyPoint S t) (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (by cases t
        · exact AffineSpace.zeroSection_comp_over _ _
        · exact AffineSpace.oneSection_comp_over _ _)
  let T' (t : Bool) : G' ⋙ H' t ≅ 𝟭 _ := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (exceptionalFamilyPoint S' t) (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')
    (by cases t
        · exact AffineSpace.zeroSection_comp_over _ _
        · exact AffineSpace.oneSection_comp_over _ _)
  let L (t : Bool) := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v
    (exceptionalFamilyPoint S t)).symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (exceptionalFamilyPoint S' t) (AffineSpace.map (ULift.{u} (Fin 1)) v)
      (v ≫ exceptionalFamilyPoint S t) (e.point_comm t)
  have hτ : P'.IsNormalized A τ := by
    exact normalized_base_transport G (H true) G' (H' true) U V
      (T true) (T' true) J (L true) b c κ
      (P.fibreMap A true) (P'.fibreMap A true) hκ.1 (hb.2 true).2.2.2 (hT true)
  have ht : τ = κ' := hκ'.2 τ hτ
  have hk : b.hom ≫ κ'.hom = V.map κ.hom ≫ j.inv ≫ G'.map c.hom := by
    rw [← ht]
    simp [τ]
  refine ⟨hk, ?_⟩
  exact specialization_base_transport G (H false) G' (H' false) U V
    (T false) (T' false) J (L false) b c κ κ'
    (P.fibreMap A false) (P'.fibreMap A false)
    (sectionExceptionalComparison A (e.fibre false)) hk (hb.2 false).2.2.2 (hT false)


/-- Uniquely normalized family isomorphisms and their specializations respect etale maps
of families. Source: blueprint sk-thm-dnc, Local construction and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence).
Proof: (10) transport kappa by the counit-normalized etale locality isomorphisms. The one-fibre
locality square makes the transported isomorphism normalized, so uniqueness identifies it
with kappa subscript one. Restrict to zero, invert, and apply the zero-fibre locality square
to obtain the specialization identity. The first equation is equivalently the stated
formula with the inverse of the ambient locality isomorphism.
-/
theorem sectionExceptional_normalized_etale
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S : Scheme.{u}} {d : ℕ} (P P₁ : ExceptionalSectionFamily S d)
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (h : ExceptionalFamilyEtaleMap P P₁)
    (κ : sectionInvariant A P.ambient.map P.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P.fibre true).map (P.fibre true).sect))
    (κ₁ : sectionInvariant A P₁.ambient.map P₁.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P₁.fibre true).map (P₁.fibre true).sect))
    (hκ : P.IsNormalized A κ ∧ ∀ τ, P.IsNormalized A τ → τ = κ)
    (hκ₁ : P₁.IsNormalized A κ₁ ∧ ∀ τ, P₁.IsNormalized A τ → τ = κ₁) :
    (sectionExceptionalLocalityIso A h.ambient).hom ≫ κ₁.hom =
      κ.hom ≫
        (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.map
            (sectionExceptionalLocalityIso A (h.fibre true)).hom ∧
    (sectionExceptionalLocalityIso A (h.fibre true)).hom ≫ P₁.specialization A κ₁ =
      P.specialization A κ ≫ (sectionExceptionalLocalityIso A (h.fibre false)).hom := by
  let G := (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor
  let b := sectionExceptionalLocalityIso A h.ambient
  let c := sectionExceptionalLocalityIso A (h.fibre true)
  let τ := b.symm ≪≫ κ ≪≫ G.mapIso c
  have hs := sectionExceptional_etale_fibre_coherence A N hN hA P P₁ hInvertible h
  have hτ : P₁.IsNormalized A τ := by
    exact normalized_transport G
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
        (AffineSpace.oneSection_comp_over _ _)) b c κ
      (P.fibreMap A true) (P₁.fibreMap A true) hκ.1 (hs true)
  have ht : τ = κ₁ := hκ₁.2 τ hτ
  have hk : b.hom ≫ κ₁.hom = κ.hom ≫ G.map c.hom := by
    rw [← ht]
    simp [τ]
  refine ⟨hk, ?_⟩
  exact specialization_transport G
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
      (AffineSpace.zeroSection_comp_over _ _)) b c κ κ₁
    (P.fibreMap A false) (P₁.fibreMap A false)
    (sectionExceptionalLocalityIso A (h.fibre false)).hom hk (hs false)

end AlgebraicGeometry.Etale
