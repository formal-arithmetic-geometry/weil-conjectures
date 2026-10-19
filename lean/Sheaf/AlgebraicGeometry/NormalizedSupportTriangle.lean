/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.AlgebraicGeometry.SupportRestrictionTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# Canonically normalized support localization

Source: Stacks Project, Tag 09XP; blueprint lem-pur-support-restriction-triangle,
all six proof steps (blueprint: lem-pur-support-restriction-triangle).

This extends the published existence interface with the injective-complex normalization
of the boundary. The ordinary arrows are uniquely fixed by the support kernel inclusions.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- Intersection of the two closed supports, as a closed immersion.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def supportIntersection {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T) :
    pullback b c ⟶ T := pullback.fst b c ≫ b

/-- Closedness of the intersection follows by base change and composition.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: the first projection is the base change of c; compose it with b. -/
@[instance]
theorem supportIntersection_closed {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    IsClosedImmersion (supportIntersection b c) := by
  dsimp [supportIntersection]
  infer_instance

/-- The support restricted to an actual open ambient scheme.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def supportOnOpen {T B : Scheme.{u}} (b : B ⟶ T) (U : T.Opens) :
    pullback b U.ι ⟶ U := pullback.snd b U.ι

/-- Closed immersions remain closed after open base change.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: this projection is the base change of b along the open immersion. -/
@[instance]
theorem supportOnOpen_closed {T B : Scheme.{u}} (b : B ⟶ T) (U : T.Opens)
    [IsClosedImmersion b] : IsClosedImmersion (supportOnOpen b U) := by
  dsimp [supportOnOpen]
  infer_instance

/-- Uniquely normalized inclusion of the intersection support kernel.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: a section vanishing off B intersection C vanishes off B. The kernel universal
property gives existence, naturality and uniqueness, since the kernel inclusion is monic. -/
theorem exists_unique_supportInclusion (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    ∃! a : supportedEtaleSections A T (supportIntersection b c).openComplement ⟶
        supportedEtaleSections A T b.openComplement,
      a ≫ supportedEtaleSectionsι A T b.openComplement =
        supportedEtaleSectionsι A T (supportIntersection b c).openComplement := by
  sorry

/-- Canonical support inclusion, selected by its unique kernel characterization.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def supportInclusion (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    supportedEtaleSections A T (supportIntersection b c).openComplement ⟶
      supportedEtaleSections A T b.openComplement :=
  (exists_unique_supportInclusion A b c).choose

/-- Canonical restriction on supported sections is uniquely fixed by restriction on
ordinary sections. Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: pullback of a supported section vanishes off the pulled-back support. Factor its
ordinary restriction through the kernel. The monic kernel inclusion gives uniqueness
and naturality. This works for every open, including the empty and full opens. -/
theorem exists_unique_supportOpenRestriction (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :
    ∃! r : supportedEtaleSections A T b.openComplement ⟶
        upperStar (ModuleCat.{u + 1} A) U.ι ⋙
          supportedEtaleSections A U (supportOnOpen b U).openComplement,
      ∀ M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
        r.app M ≫ (supportedEtaleSectionsι A U (supportOnOpen b U).openComplement).app
            ((upperStar (ModuleCat.{u + 1} A) U.ι).obj M) =
          (supportedEtaleSectionsι A T b.openComplement).app M ≫
            globalSectionsUpperStarMap (ModuleCat.{u + 1} A) U.ι M := by
  sorry

/-- Restriction with support to an open ambient scheme.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def supportOpenRestriction (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :
    supportedEtaleSections A T b.openComplement ⟶
      upperStar (ModuleCat.{u + 1} A) U.ι ⋙
        supportedEtaleSections A U (supportOnOpen b U).openComplement :=
  (exists_unique_supportOpenRestriction A b U).choose

/-- The composite of intersection inclusion and restriction to T minus C is zero.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: its sections vanish on T minus C. Compose with the monic support kernel inclusion
and use the characterizations of both arrows to obtain the zero restriction. -/
theorem supportInclusion_restriction_zero (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    supportInclusion A b c ≫ supportOpenRestriction A b c.openComplement = 0 := by
  sorry

/-- The ordinary support localization short complex of functors.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def supportLocalizationSequence (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :=
  ShortComplex.mk (supportInclusion A b c) (supportOpenRestriction A b c.openComplement)
    (supportInclusion_restriction_zero A b c)

/-- Termwise localization of a complex of sheaves.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def supportLocalizationComplex (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u + 1} A) ℤ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (supportInclusion A b c) (.up ℤ)).app I)
    ((NatTrans.mapHomologicalComplex (supportOpenRestriction A b c.openComplement)
      (.up ℤ)).app I)
    (by
      ext n : 1
      exact NatTrans.congr_app (supportInclusion_restriction_zero A b c) (I.X n))

/-- Injective sheaves give a short exact sequence of supported section complexes.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: restriction is onto by extending a section supported on B intersection U by zero
on T minus B, gluing on their union, and lifting that section to T by injectivity and the
extension-by-zero adjunction. The kernel is the intersection support. Apply degreewise. -/
theorem supportLocalizationComplex_shortExact (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [∀ n : ℤ, Injective (I.X n)] : (supportLocalizationComplex A b c I).ShortExact := by
  sorry

/-- The derived functor of the third ordinary support functor before the canonical
open-restriction comparison. Source: Tag 09XP
(blueprint: lem-pur-support-restriction-triangle). -/
noncomputable abbrev supportOpenComposite (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :=
  upperStar (ModuleCat.{u + 1} A) U.ι ⋙
    supportedEtaleSections A U (supportOnOpen b U).openComplement

/-- The canonical boundary, normalized on every termwise injective K-injective complex.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: the short exact complex gives its canonical connecting map. Naturality of the
short exact complex triangle descends this to the derived category. Every derived object
has a termwise injective K-injective resolution, and the K-injective Hom bijection shows
both independence of resolutions and uniqueness with the stated normalization. -/
theorem exists_unique_supportLocalizationBoundary (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    ∃! δ : (supportOpenComposite A b c.openComplement).rightDerivedFunctor ⟶
        (supportedEtaleSections A T (supportIntersection b c).openComplement).rightDerivedFunctor
          ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (1 : ℤ),
      ∀ (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)],
        δ.app (DerivedCategory.Q.obj I) ≫
            ((supportedEtaleSections A T (supportIntersection b
              c).openComplement).rightDerivedFunctorObjQIso I).hom⟦1⟧' =
          ((supportOpenComposite A b c.openComplement).rightDerivedFunctorObjQIso I).hom ≫
            DerivedCategory.triangleOfSESδ (supportLocalizationComplex_shortExact A b c I) := by
  sorry

/-- The normalized connecting map, with no arbitrary triangle completion.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def supportLocalizationBoundary (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    (supportOpenComposite A b c.openComplement).rightDerivedFunctor ⟶
      (supportedEtaleSections A T (supportIntersection b c).openComplement).rightDerivedFunctor ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (1 : ℤ) :=
  (exists_unique_supportLocalizationBoundary A b c).choose

/-- Canonical comparison for restriction to an open before taking supported sections.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: open inverse image is exact and preserves injectives, being right adjoint to
exact extension by zero. The composition theorem for right derived functors gives the
comparison. The uniqueness of derived functors characterizes it by the displayed units. -/
theorem exists_unique_supportOpenDerivedComparison (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :
    ∃! e : (supportOpenComposite A b U).rightDerivedFunctor ≅
        (upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory ⋙
          supportedSectionsDerived A (supportOnOpen b U),
      (supportOpenComposite A b U).rightDerivedFunctorUnit ≫
          Functor.whiskerLeft DerivedCategory.Qh e.hom =
        Functor.rightDerivedFunctorCompUnit (upperStar (ModuleCat.{u + 1} A) U.ι)
            (supportedEtaleSections A U (supportOnOpen b U).openComplement) ≫
          Functor.whiskerLeft DerivedCategory.Qh
            (Functor.whiskerRight
              ((upperStar (ModuleCat.{u + 1} A) U.ι).rightDerivedFunctorIsoMapDerivedCategory).hom
              (supportedSectionsDerived A (supportOnOpen b U))) := by
  let F := upperStar (ModuleCat.{u + 1} A) U.ι
  let G := supportedEtaleSections A U (supportOnOpen b U).openComplement
  let adj := etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) U.ι
    (inferInstance : Etale U.ι)
  have : (etaleLowerShriek (ModuleCat.{u + 1} A) U.ι inferInstance).Additive :=
    adj.left_adjoint_additive
  have : F.PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  let e := F.rightDerivedFunctorCompIso G ≪≫
    Functor.isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor
  have he : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh e.hom =
      Functor.rightDerivedFunctorCompUnit F G ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.hom
            G.rightDerivedFunctor) := by
    simp [e, Functor.rightDerivedFunctorCompIso, Functor.whiskerLeft_comp]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (F ⋙ G).rightDerivedFunctor.rightDerived_ext
    (F ⋙ G).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso _ (.up ℤ))
  exact he'.trans he.symm

/-- The uniquely normalized derived open comparison.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def supportOpenDerivedComparison (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :
    (supportOpenComposite A b U).rightDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory ⋙
        supportedSectionsDerived A (supportOnOpen b U) :=
  (exists_unique_supportOpenDerivedComparison A b U).choose

/-- The derived restriction arrow, with the third term on the open ambient scheme.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def derivedSupportOpenRestriction (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :=
  Functor.rightDerivedFunctorNatTrans (supportOpenRestriction A b U) ≫
    (supportOpenDerivedComparison A b U).hom

/-- Localization triangle with the actual support inclusion, restriction, and boundary.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def normalizedSupportTriangle (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Triangle (DerivedCategory (ModuleCat.{u + 1} A)) :=
  Triangle.mk ((Functor.rightDerivedFunctorNatTrans (supportInclusion A b c)).app K)
    ((derivedSupportOpenRestriction A b c.openComplement).app K)
    ((supportOpenDerivedComparison A b c.openComplement).inv.app K ≫
      (supportLocalizationBoundary A b c).app K)

/-- The normalized triangle is distinguished and specializes to the recorded D+ triangle.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: compute all three functors on a termwise injective K-injective resolution. The
boundary normalization identifies this triangle with the short exact complex triangle,
which is distinguished. Bounded-below injective resolutions give the earlier D+ form
through rightDerivedFunctorPlusCompatibility and exact open inverse image. -/
theorem normalizedSupportTriangle_distinguished (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    normalizedSupportTriangle A b c K.obj ∈ distTriang (DerivedCategory (ModuleCat.{u + 1} A)) := by
  sorry

/-- The complement of a support after open base change.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: a point lies off the base-changed closed subscheme exactly when its image lies
off the original closed subscheme, by the topological image description of base change. -/
theorem supportOnOpen_complement {T B : Scheme.{u}} (b : B ⟶ T)
    [IsClosedImmersion b] (U : T.Opens) :
    (supportOnOpen b U).openComplement = U.ι ⁻¹ᵁ b.openComplement := by
  apply TopologicalSpace.Opens.ext
  change (Set.range (pullback.snd b U.ι))ᶜ = U.ι ⁻¹' (Set.range b)ᶜ
  rw [Scheme.Pullback.range_snd]
  rfl

/-- Supported pullback along an open immersion, normalized on ordinary sections.
Source: Tag 09XP, restriction construction
(blueprint: lem-pur-support-restriction-triangle).
Proof: the complement equality makes restriction land in the support kernel. Its monic
inclusion gives existence and uniqueness of the natural transformation. -/
theorem exists_unique_supportTransport (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (_hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    ∃! r : supportedEtaleSections A T b.openComplement ⟶
        upperStar (ModuleCat.{u + 1} A) h ⋙ supportedEtaleSections A S d.openComplement,
      ∀ M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
        r.app M ≫ (supportedEtaleSectionsι A S d.openComplement).app
            ((upperStar (ModuleCat.{u + 1} A) h).obj M) =
          (supportedEtaleSectionsι A T b.openComplement).app M ≫
            globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h M := by
  sorry

/-- The uniquely normalized ordinary supported transport.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def supportTransport (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    supportedEtaleSections A T b.openComplement ⟶
      upperStar (ModuleCat.{u + 1} A) h ⋙ supportedEtaleSections A S d.openComplement :=
  (exists_unique_supportTransport A h b d hd).choose

/-- Canonical derived-composite comparison for an open immersion.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: exact extension by zero is left adjoint to open inverse image, so the latter
preserves injectives and K-injectives. Apply the derived-composition theorem and exact
pullback comparison. Uniqueness of right derived functors gives the unit normalization. -/
theorem exists_unique_supportTransportComparison (A : Type (u + 1)) [CommRing A]
    {T S D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (d : D ⟶ S) [IsClosedImmersion d] :
    ∃! e : (upperStar (ModuleCat.{u + 1} A) h ⋙
        supportedEtaleSections A S d.openComplement).rightDerivedFunctor ≅
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ⋙ supportedSectionsDerived A d,
      (upperStar (ModuleCat.{u + 1} A) h ⋙
          supportedEtaleSections A S d.openComplement).rightDerivedFunctorUnit ≫
          Functor.whiskerLeft DerivedCategory.Qh e.hom =
        Functor.rightDerivedFunctorCompUnit (upperStar (ModuleCat.{u + 1} A) h)
            (supportedEtaleSections A S d.openComplement) ≫
          Functor.whiskerLeft DerivedCategory.Qh (Functor.whiskerRight
            (upperStar (ModuleCat.{u + 1} A) h).rightDerivedFunctorIsoMapDerivedCategory.hom
            (supportedSectionsDerived A d)) := by
  let F := upperStar (ModuleCat.{u + 1} A) h
  let G := supportedEtaleSections A S d.openComplement
  let adj := etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) h
    (inferInstance : Etale h)
  have : (etaleLowerShriek (ModuleCat.{u + 1} A) h inferInstance).Additive :=
    adj.left_adjoint_additive
  have : F.PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  let e := F.rightDerivedFunctorCompIso G ≪≫
    Functor.isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor
  have he : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh e.hom =
      Functor.rightDerivedFunctorCompUnit F G ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.hom
            G.rightDerivedFunctor) := by
    simp [e, Functor.rightDerivedFunctorCompIso, Functor.whiskerLeft_comp]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (F ⋙ G).rightDerivedFunctor.rightDerived_ext
    (F ⋙ G).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso _ (.up ℤ))
  exact he'.trans he.symm

/-- The normalized derived-composite comparison for an open immersion.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def supportTransportComparison (A : Type (u + 1)) [CommRing A]
    {T S D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (d : D ⟶ S) [IsClosedImmersion d] :
    (upperStar (ModuleCat.{u + 1} A) h ⋙
      supportedEtaleSections A S d.openComplement).rightDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ⋙ supportedSectionsDerived A d :=
  (exists_unique_supportTransportComparison A h d).choose

/-- The actual derived restriction with closed support, to an arbitrary open immersion.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def derivedSupportTransport (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :=
  Functor.rightDerivedFunctorNatTrans (supportTransport A h b d hd) ≫
    (supportTransportComparison A h d).hom

/-- Change of ambient scheme by an isomorphism is an isomorphism on derived supports.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle).
Proof: inverse image along a scheme isomorphism is an equivalence. Its global-sections
map is invertible, hence so is the map of the support kernels. Derive this isomorphism
and compose with the canonical derived-composite comparison. -/
@[instance]
theorem derivedSupportTransport_isIso (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsIso h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    IsIso (derivedSupportTransport A h b d hd) := by
  sorry

/-- Support invariance uses equality of open complements of the two closed supports.
Source: Tag 09XP (blueprint: lem-pur-support-restriction-triangle). -/
noncomputable def derivedSupportCongruence (A : Type (u + 1)) [CommRing A]
    {T B D : Scheme.{u}} (b : B ⟶ T) (d : D ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion d] (hd : b.openComplement = d.openComplement) :
    supportedSectionsDerived A b ≅ supportedSectionsDerived A d :=
  Functor.rightDerivedFunctorNatIso
    (eqToIso (congrArg (supportedEtaleSections A T) hd))

end AlgebraicGeometry.Etale
