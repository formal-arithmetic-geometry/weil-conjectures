/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.DerivedNormalizationArrows
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Sheafification

/-! # The sheaf of derived local isomorphisms

Source: Stacks Project, Tag 09BV, isomorphism sheaves, with the bounded-derived adaptation
of lem-weil-pbc-compatible-finite-derived-trivializations
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf).

The presheaf uses actual isomorphisms in the derived categories of the localized etale
sites, identified with the sites of the source schemes. Its restriction maps are the
canonical exact pullbacks, transported by their composition comparisons.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

/-- Derived restriction of fixed-coefficient sheaves to an etale object, using the
existing exact inverse image. Source: Stacks Tag 03ED
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable abbrev localIsomorphismRestriction (V : X.Etale) :=
  (Etale.upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory

/-- Canonical comparison for successive etale restrictions.
Source: Stacks Tags 03ED and 05RU
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localIsomorphismRestrictionComp {V W : X.Etale} (f : V ⟶ W) :
    localIsomorphismRestriction X B V ≅ localIsomorphismRestriction X B W ⋙
      (Etale.upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso
    (Etale.upperStarComp (ModuleCat.{u + 1} B) f.left W.hom V.hom f.w.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

variable {X B}

/-- Restrict an actual local derived isomorphism along an arrow of the etale site.
Source: Stacks Tag 09BV, derived adaptation
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localIsomorphismMap
    (A K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    {V W : X.Etale} (f : V ⟶ W)
    (e : (localIsomorphismRestriction X B W).obj A ≅
      (localIsomorphismRestriction X B W).obj K) :
    (localIsomorphismRestriction X B V).obj A ≅
      (localIsomorphismRestriction X B V).obj K :=
  (localIsomorphismRestrictionComp X B f).app A ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.mapIso e ≪≫
    ((localIsomorphismRestrictionComp X B f).app K).symm

/-- The canonical local restriction maps obey the presheaf laws.
Source: Stacks Tags 03ED and 09BV, derived adaptation
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf).
Proof: the underived inverse images have the identity and associativity comparisons
obtained from their adjunctions. Localization carries these comparisons and their
coherence identities to the derived category. In the conjugation defining the displayed
restriction map the intermediate comparison and its inverse cancel. The identity law
then follows from the identity comparison, and the composition law from associativity.
This applies to all derived objects and isomorphisms, without a boundedness assumption. -/
theorem localIsomorphismMap_laws
    (A K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (∀ (V : X.Etale) (e : (localIsomorphismRestriction X B V).obj A ≅
      (localIsomorphismRestriction X B V).obj K), localIsomorphismMap A K (𝟙 V) e = e) ∧
    (∀ {U V W : X.Etale} (f : U ⟶ V) (g : V ⟶ W)
      (e : (localIsomorphismRestriction X B W).obj A ≅
        (localIsomorphismRestriction X B W).obj K),
      localIsomorphismMap A K (f ≫ g) e =
        localIsomorphismMap A K f (localIsomorphismMap A K g e)) := by
  sorry

/-- The presheaf of isomorphisms in the derived categories of localized etale sites.
Source: Stacks Tag 09BV, derived adaptation
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def derivedLocalIsomorphismPresheaf
    (A K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    X.Etaleᵒᵖ ⥤ Type (u + 1) where
  obj V := (localIsomorphismRestriction X B V.unop).obj A ≅
    (localIsomorphismRestriction X B V.unop).obj K
  map f := TypeCat.ofHom (localIsomorphismMap A K f.unop)
  map_id V := ConcreteCategory.hom_ext _ _ ((localIsomorphismMap_laws A K).1 V.unop)
  map_comp f g := ConcreteCategory.hom_ext _ _ ((localIsomorphismMap_laws A K).2 g.unop f.unop)

/-- The sheafification of actual local derived isomorphisms; no arbitrary sheaf or
comparison map is chosen. Source: Stacks Tag 09BV, derived adaptation
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def derivedLocalIsomorphismSheaf
    (A K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  (presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj
    (derivedLocalIsomorphismPresheaf A K)

section ProEtale

variable {Y : Scheme.{u}} (f : Y ⟶ X) {R S : Type (u + 1)} [CommRing R] [CommRing S]

/-- Derived comparison followed by derived restriction to a pro-etale object. The same
formula is defined for any scheme map, with no change to the chosen derived categories.
Source: Stacks Tags 099R and 098K
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable abbrev localProEtaleComparison (R : Type (u + 1)) [CommRing R] :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory ⋙
    (ProEtale.upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory

/-- The canonical comparison/coefficients interchange, obtained by localizing the mate
of sectionwise restriction. Source: Stacks Tags 099R and 03DA
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localIsomorphismComparisonCoefficients (q : R →+* S) :
    normalizationRestrict X.smallEtaleTopology q ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X).mapDerivedCategory ⋙
        normalizationRestrict (ProEt.topology X) q :=
  (Functor.mapDerivedCategoryCompIso
    (sheafCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X)).symm ≪≫
  Functor.mapDerivedCategoryNatIso
    (F := sheafCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X)
    (G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X ⋙
      sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
    (normalizationPullbackIso X.smallEtaleTopology (toProEt X) (ProEt.topology X) q :
      sheafCompose X.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X ≅
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X ⋙
        sheafCompose (ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) ≪≫
  Functor.mapDerivedCategoryCompIso
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X)
    (sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))

/-- The canonical pro-etale restriction/coefficients interchange, again the localization
of the specified mate. Source: Stacks Tags 098K and 03DA
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localIsomorphismProEtaleCoefficients (q : R →+* S) :
    normalizationRestrict (ProEt.topology X) q ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} S) f).mapDerivedCategory ⋙
        normalizationRestrict (ProEt.topology Y) q :=
  letI := ProEt.isContinuous_overPullback f
  (Functor.mapDerivedCategoryCompIso
    (sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
    (ProEtale.upperStar (ModuleCat.{u + 1} R) f)).symm ≪≫
  Functor.mapDerivedCategoryNatIso
    (F := sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} R) f)
    (G := ProEtale.upperStar (ModuleCat.{u + 1} S) f ⋙
      sheafCompose (ProEt.topology Y)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (ProEt.topology Y) q :
      sheafCompose (ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} R) f ≅
      ProEtale.upperStar (ModuleCat.{u + 1} S) f ⋙
        sheafCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) ≪≫
  Functor.mapDerivedCategoryCompIso
    (ProEtale.upperStar (ModuleCat.{u + 1} S) f)
    (sheafCompose (ProEt.topology Y)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))

/-- Combined canonical coefficient interchange for comparison and local restriction.
Source: Stacks Tags 099R and 098K
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localProEtaleComparisonCoefficients (q : R →+* S) :
    normalizationRestrict X.smallEtaleTopology q ⋙ localProEtaleComparison f R ≅
      localProEtaleComparison f S ⋙ normalizationRestrict (ProEt.topology Y) q :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (localIsomorphismComparisonCoefficients q) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (localIsomorphismProEtaleCoefficients f q) ≪≫
    (Functor.associator _ _ _).symm

/-- Pull a specified normalization arrow to the localized pro-etale site. This is its
actual inverse image followed by the canonical coefficient interchange, not an arbitrary
arrow with the same endpoints. Source: Stacks Tags 099R, 098K and 06YY
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localProEtaleNormalization (q : R →+* S)
    {A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (d : A ⟶ (normalizationRestrict X.smallEtaleTopology q).obj K) :
    (localProEtaleComparison f R).obj A ⟶
      (normalizationRestrict (ProEt.topology Y) q).obj
        ((localProEtaleComparison f S).obj K) :=
  (localProEtaleComparison f R).map d ≫
    (localProEtaleComparisonCoefficients f q).hom.app K

end ProEtale

end AlgebraicGeometry.Scheme

