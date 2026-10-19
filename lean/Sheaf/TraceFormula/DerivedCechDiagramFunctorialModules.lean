/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.RGammaUnboundedWellDefined
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Compatible roofs for restriction of resolved cosimplicial module complexes

Source: literature/stacks-project/derived.tex, Tag 0141,
lemma-functorial-injective-resolutions and remark-match
(blueprint: lem-trf-derived-cech-diagram-functorial-modules).

The resolution functors have domain `CochainComplex.Plus`, exactly as in the cited
resolution theorem. The helpers describe the four vertices, canonical arrows, lower
bounds, and the normalized comparison with the existing unbounded derived sections.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

namespace AlgebraicGeometry.Etale

/-- Apply a chosen bounded-below resolution, forget the bound, and take sections, over
an entire augmented diagram. Source: Stacks Tag 0141, diagramwise functoriality
(blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
noncomputable def resolvedCechDiagram
    (Λ : Type (u + 1)) [CommRing Λ] (Y : Scheme.{u})
    (I : CochainComplex.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      CochainComplex.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  CosimplicialObject.Augmented.whiskeringObj _ _
    (I ⋙ CochainComplex.Plus.ι _ ⋙
      (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ))

/-- Exact inverse image applied to a whole augmented bounded-below diagram. Source:
Stacks Tags 04JC and 0141 (blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
noncomputable def pulledCechDiagram
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) :=
  CosimplicialObject.Augmented.whiskeringObj _ _
    (Etale.upperStar (ModuleCat.{u + 1} Λ) h).mapCochainComplexPlus

/-- A column indexed by `none` is the augmentation, and one indexed by `some q` is the
ordinary cosimplicial column `q`. Source: Stacks Tag 0141, augmented diagram application
(blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
def augmentedCechColumn {C : Type u} [Category.{v} C]
    (A : CosimplicialObject.Augmented C) : Option SimplexCategory → C
  | none => A.left
  | some q => A.right.obj q

/-- Evaluation of an augmented diagram morphism, including its augmentation. Source:
Stacks Tag 0141, diagramwise naturality
(blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
def augmentedCechColumnMap {C : Type u} [Category.{v} C]
    {A B : CosimplicialObject.Augmented C} (f : A ⟶ B) :
    ∀ q : Option SimplexCategory, augmentedCechColumn A q ⟶ augmentedCechColumn B q
  | none => f.left
  | some q => f.right.app q

/-- The unit comparison from sections of a complex to its derived sections. It is the
existing right-derived-functor unit, transported through the canonical comparison between
`Q` and quotient followed by `Qh`. Source: Stacks Tag 070I and Tag 0141, remark-match
(blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
noncomputable def resolvedCechSectionsToDerived
    (Λ : Type (u + 1)) [CommRing Λ]
    (Y : Scheme.{u})
    (K : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    DerivedCategory.Q.obj
        (((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj
        (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} Λ)).inv.app _ ≫
    DerivedCategory.Qh.map
      (((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app K) ≫
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K) ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
      ((DerivedCategory.quotientCompQhIso _).hom.app K)

variable (Λ : Type (u + 1)) [CommRing Λ]
    (Y Y' : Scheme.{u}) (h : Y' ⟶ Y)
    (I : CochainComplex.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      CochainComplex.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (I' : CochainComplex.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      CochainComplex.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (A : CosimplicialObject.Augmented
      (CochainComplex.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (B : CosimplicialObject.Augmented
      (CochainComplex.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))))

/-- The three actual augmented-diagram arrows in the common-resolution roof, with their
prescribed four vertices. Source: Stacks Tag 0141, diagramwise application across exact
inverse image (blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
structure CompatibleRoof where
  u : (resolvedCechDiagram Λ Y I).obj A ⟶
    (resolvedCechDiagram Λ Y' I').obj
      ((pulledCechDiagram Λ h).obj
        ((CosimplicialObject.Augmented.whiskeringObj _ _ I).obj A))
  v : (resolvedCechDiagram Λ Y' I').obj ((pulledCechDiagram Λ h).obj A) ⟶
    (resolvedCechDiagram Λ Y' I').obj
      ((pulledCechDiagram Λ h).obj
        ((CosimplicialObject.Augmented.whiskeringObj _ _ I).obj A))
  w : (resolvedCechDiagram Λ Y' I').obj ((pulledCechDiagram Λ h).obj A) ⟶
    (resolvedCechDiagram Λ Y' I').obj B

/-- All four displayed vertices have the same internal lower bound, including their
augmentation columns. Source: Stacks Tag 0141, preservation of lower bounds
(blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
def CompatibleRoofColumnsGE (a : ℤ) : Prop :=
  ∀ D ∈ [(resolvedCechDiagram Λ Y I).obj A,
    (resolvedCechDiagram Λ Y' I').obj ((pulledCechDiagram Λ h).obj A),
    (resolvedCechDiagram Λ Y' I').obj
      ((pulledCechDiagram Λ h).obj
        ((CosimplicialObject.Augmented.whiskeringObj _ _ I).obj A)),
    (resolvedCechDiagram Λ Y' I').obj B],
    ∀ q : Option SimplexCategory, CochainComplex.IsStrictlyGE (augmentedCechColumn D q) a

/-- The restriction arrow is the section pullback followed by the resolution unit in
both ordinary and augmentation columns. Source: Stacks Tag 0141, naturality of the units;
section pullback is the adjunction unit at the terminal object (Tag 04JC)
(blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
def CanonicalRoofU
    (η' : CochainComplex.Plus.ι _ ⟶ I' ⋙ CochainComplex.Plus.ι _)
    (R : CompatibleRoof Λ Y Y' h I I' A B) : Prop :=
  ∀ q : Option SimplexCategory,
    match q with
    | none =>
      ∀ i : ℤ,
        (augmentedCechColumnMap R.u none).f i =
          globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) h
              ((I.obj (augmentedCechColumn A none)).obj.X i) ≫
            (Sheaf.Γ Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
              ((η'.app ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).mapCochainComplexPlus.obj
                (I.obj (augmentedCechColumn A none)))).f i)
    | some q =>
      ∀ i : ℤ,
        (augmentedCechColumnMap R.u (some q)).f i =
          globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) h
              ((I.obj (augmentedCechColumn A (some q))).obj.X i) ≫
            (Sheaf.Γ Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
              ((η'.app ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).mapCochainComplexPlus.obj
                (I.obj (augmentedCechColumn A (some q))))).f i)


/-- The middle arrow is sections of `I'` applied to the exact pullback of the resolution
unit. The full-subcategory morphism is its actual underlying chain map. Source: Stacks
Tag 0141, remark-match (blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
def CanonicalRoofV
    (η : CochainComplex.Plus.ι _ ⟶ I ⋙ CochainComplex.Plus.ι _)
    (R : CompatibleRoof Λ Y Y' h I I' A B) : Prop :=
  ∀ q : Option SimplexCategory,
    match q with
    | none =>
      ∀ i : ℤ,
        (augmentedCechColumnMap R.v none).f i =
          (Sheaf.Γ Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            ((I'.map ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).mapCochainComplexPlus.map
              (ObjectProperty.homMk (η.app (augmentedCechColumn A none))))).hom.f i)
    | some q =>
      ∀ i : ℤ,
        (augmentedCechColumnMap R.v (some q)).f i =
          (Sheaf.Γ Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            ((I'.map ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).mapCochainComplexPlus.map
              (ObjectProperty.homMk (η.app (augmentedCechColumn A (some q)))))).hom.f i)


/-- Columnwise identification with the derived restriction followed by `RΓ(b)`. The
isomorphisms from the chosen section models to `RΓ` are normalized by the derived-functor
unit, so they cannot be arbitrary isomorphisms. The restriction on the right is written
as the existing derived adjunction unit followed by the existing Leray isomorphism;
the exact-functor comparison transports its target to `Q(h⁻¹ A_q)`.
Source: Stacks Tag 0141, remark-match, and Tag 070I; the unit formula of node proof step 6
(blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
def CompatibleRoofDerivedIdentification
    (η : CochainComplex.Plus.ι _ ⟶ I ⋙ CochainComplex.Plus.ι _)
    (η' : CochainComplex.Plus.ι _ ⟶ I' ⋙ CochainComplex.Plus.ι _)
    (b : (pulledCechDiagram Λ h).obj A ⟶ B)
    (R : CompatibleRoof Λ Y Y' h I I' A B) : Prop :=
  ∀ q : Option SimplexCategory,
    match q with
    | none =>
      ∃ (r : DerivedCategory.Q.obj
            (augmentedCechColumn
              ((resolvedCechDiagram Λ Y' I').obj
                ((pulledCechDiagram Λ h).obj
                  ((CosimplicialObject.Augmented.whiskeringObj _ _ I).obj A))) none) ⟶
          DerivedCategory.Q.obj
            (augmentedCechColumn
              ((resolvedCechDiagram Λ Y' I').obj ((pulledCechDiagram Λ h).obj A)) none))
        (eA : DerivedCategory.Q.obj
            (augmentedCechColumn ((resolvedCechDiagram Λ Y I).obj A) none) ≅
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj
            (DerivedCategory.Q.obj (augmentedCechColumn A none).obj))
        (eB : DerivedCategory.Q.obj
            (augmentedCechColumn ((resolvedCechDiagram Λ Y' I').obj B) none) ≅
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y').obj
            (DerivedCategory.Q.obj (augmentedCechColumn B none).obj)),
        DerivedCategory.Q.map (augmentedCechColumnMap R.v none) ≫ r = 𝟙 _ ∧
        r ≫ DerivedCategory.Q.map (augmentedCechColumnMap R.v none) = 𝟙 _ ∧
        eA.hom ≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
            (DerivedCategory.Q.map (η.app (augmentedCechColumn A none))) =
          resolvedCechSectionsToDerived Λ Y (I.obj (augmentedCechColumn A none)).obj ∧
        eB.hom ≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y').map
            (DerivedCategory.Q.map (η'.app (augmentedCechColumn B none))) =
          resolvedCechSectionsToDerived Λ Y' (I'.obj (augmentedCechColumn B none)).obj ∧
        DerivedCategory.Q.map (augmentedCechColumnMap R.u none) ≫ r ≫
            DerivedCategory.Q.map (augmentedCechColumnMap R.w none) ≫ eB.hom =
          eA.hom ≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
              ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
                (DerivedCategory.Q.obj (augmentedCechColumn A none).obj)) ≫
            (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
              (ModuleCat.{u + 1} Λ) h).hom.app _ ≫
            (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y').map
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).mapDerivedCategoryFactors.hom.app
                  (augmentedCechColumn A none).obj ≫
                DerivedCategory.Q.map (augmentedCechColumnMap b none).hom)
    | some q =>
      ∃ (r : DerivedCategory.Q.obj
            (augmentedCechColumn
              ((resolvedCechDiagram Λ Y' I').obj
                ((pulledCechDiagram Λ h).obj
                  ((CosimplicialObject.Augmented.whiskeringObj _ _ I).obj A))) (some q)) ⟶
          DerivedCategory.Q.obj
            (augmentedCechColumn
              ((resolvedCechDiagram Λ Y' I').obj ((pulledCechDiagram Λ h).obj A)) (some q)))
        (eA : DerivedCategory.Q.obj
            (augmentedCechColumn ((resolvedCechDiagram Λ Y I).obj A) (some q)) ≅
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj
            (DerivedCategory.Q.obj (augmentedCechColumn A (some q)).obj))
        (eB : DerivedCategory.Q.obj
            (augmentedCechColumn ((resolvedCechDiagram Λ Y' I').obj B) (some q)) ≅
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y').obj
            (DerivedCategory.Q.obj (augmentedCechColumn B (some q)).obj)),
        DerivedCategory.Q.map (augmentedCechColumnMap R.v (some q)) ≫ r = 𝟙 _ ∧
        r ≫ DerivedCategory.Q.map (augmentedCechColumnMap R.v (some q)) = 𝟙 _ ∧
        eA.hom ≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
            (DerivedCategory.Q.map (η.app (augmentedCechColumn A (some q)))) =
          resolvedCechSectionsToDerived Λ Y (I.obj (augmentedCechColumn A (some q))).obj ∧
        eB.hom ≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y').map
            (DerivedCategory.Q.map (η'.app (augmentedCechColumn B (some q)))) =
          resolvedCechSectionsToDerived Λ Y' (I'.obj (augmentedCechColumn B (some q))).obj ∧
        DerivedCategory.Q.map (augmentedCechColumnMap R.u (some q)) ≫ r ≫
            DerivedCategory.Q.map (augmentedCechColumnMap R.w (some q)) ≫ eB.hom =
          eA.hom ≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
              ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
                (DerivedCategory.Q.obj (augmentedCechColumn A (some q)).obj)) ≫
            (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
              (ModuleCat.{u + 1} Λ) h).hom.app _ ≫
            (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y').map
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).mapDerivedCategoryFactors.hom.app
                  (augmentedCechColumn A (some q)).obj ≫
                DerivedCategory.Q.map (augmentedCechColumnMap b (some q)).hom)

/-- The actual alternating-coface double-complex maps obtained from a compatible roof.
Their horizontal degree is the cosimplicial degree `q` and their vertical degree is the
internal degree. Thus their chain-map equations preserve `δ + (-1)^q d`; the original
roof also retains the augmentation and every codegeneracy. Source: Stacks Tag 0141,
diagramwise application and the alternating-coface construction
(blueprint: lem-trf-derived-cech-diagram-functorial-modules). -/
noncomputable def CompatibleRoof.alternatingMaps
    (R : CompatibleRoof Λ Y Y' h I I' A B) :=
  (AlgebraicTopology.alternatingCofaceMapComplex _ |>.map R.u.right,
    AlgebraicTopology.alternatingCofaceMapComplex _ |>.map R.v.right,
    AlgebraicTopology.alternatingCofaceMapComplex _ |>.map R.w.right)

/-- A compatible common-resolution roof, with its canonical arrows, common lower bound,
column quasi-isomorphisms, and normalized derived identification in every column.
Source: Stacks Project, `derived.tex`, Tag 0141, lemma-functorial-injective-resolutions
and remark-match (blueprint: lem-trf-derived-cech-diagram-functorial-modules).

Proof:
1. The module-sheaf categories are Grothendieck abelian by
   lem-weil-pbc-module-sheaves-grothendieck-abelian; functorial injective embeddings
   come from lem-weil-pbc-grothendieck-functorial-injective-embedding. The supplied
   `I, η, I', η'` are precisely the functors on `Plus` and natural quasi-isomorphisms
   of lem-weil-pbc-functorial-bounded-injective-resolution. Postcompose the augmented
   diagrams with these functors; naturality preserves all their structure maps.
2. By prop-weil-pbc-inverse-image-modules-exact the module inverse image is exact.
   It preserves the common termwise lower bound and the quasi-isomorphism `η`.
   Naturality of `η'` and two-out-of-three show that `I'(h⁻¹η)` is a quasi-isomorphism.
   Its source and target are bounded-below complexes of injectives, hence K-injective
   by prop-weil-pbc-kinjective-resolutions-exist. Their comparison over `h⁻¹ A_q`
   therefore remains an isomorphism after sections and localization, by
   lem-kun-rgamma-unbounded-well-defined. This makes every column of `v` a
   quasi-isomorphism of module complexes, including `q = none`.
3. Restriction on sections is `globalSectionsUpperStarMap`, the underived adjunction
   unit evaluated at the terminal object. Compose with sections of `η'` to construct
   `u`; construct `v` from `I'(h⁻¹η)` and `w` by applying `I'` and sections to the
   entire morphism `b`. Naturality makes all three augmented diagram morphisms,
   simultaneously for all cofaces, codegeneracies, and augmentation maps.
4. The lower-bound hypotheses for the supplied functors, exact pullback, and sections
   imply `CompatibleRoofColumnsGE` for all four vertices. In particular the zero
   complex and every integer lower bound are admitted. Applying Mathlib's alternating
   coface functor gives `CompatibleRoof.alternatingMaps`; the internal chain-map
   equations and coface naturality give maps for total differential `δ + (-1)^q d`.
5. By def-kun-rgamma-unbounded each injective bounded-below column computes the
   existing `rightDerivedGlobalSections`. Normalize these identifications using its
   unit, giving `eA, eB` in `CompatibleRoofDerivedIdentification`. The column `u`
   computes restriction via the inverse-image/direct-image unit and Leray; exactness
   of pullback identifies the pulled-back representative with derived pullback.
6. By lem-kun-rgamma-unbounded-well-defined, `v` is the canonical comparison between
   the two resolutions of `h⁻¹ A_q`; its inverse is the `r` in the predicate.
   Naturality of `η'` makes `w` the lift of `b_q`, hence its image is `RΓ(b_q)`.
   Compose to obtain the displayed equality for every `some q` and for `none`.
   One augmented roof supplies all columns, rather than unrelated derived choices. -/
theorem compatible_roof_of_augmented_cosimplicial_module_complexes
    (Λ : Type (u + 1)) [CommRing Λ]
    (Y Y' : Scheme.{u}) (h : Y' ⟶ Y)
    (I : CochainComplex.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      CochainComplex.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (I' : CochainComplex.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      CochainComplex.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (A : CosimplicialObject.Augmented
      (CochainComplex.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (B : CosimplicialObject.Augmented
      (CochainComplex.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (η : CochainComplex.Plus.ι _ ⟶ I ⋙ CochainComplex.Plus.ι _)
    (hηq : ∀ K : CochainComplex.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)), QuasiIso (η.app K))
    (hI : ∀ (K : CochainComplex.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ),
      Injective ((I.obj K).obj.X n))
    (hIbound : ∀ (K : CochainComplex.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ),
      K.obj.IsStrictlyGE n → (I.obj K).obj.IsStrictlyGE n)
    (η' : CochainComplex.Plus.ι _ ⟶ I' ⋙ CochainComplex.Plus.ι _)
    (hη'q : ∀ K : CochainComplex.Plus
      (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)), QuasiIso (η'.app K))
    (hI' : ∀ (K : CochainComplex.Plus
      (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ),
      Injective ((I'.obj K).obj.X n))
    (hI'bound : ∀ (K : CochainComplex.Plus
      (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ),
      K.obj.IsStrictlyGE n → (I'.obj K).obj.IsStrictlyGE n)
    (b : (pulledCechDiagram Λ h).obj A ⟶ B) (a : ℤ)
    (hA : ∀ q : Option SimplexCategory, (augmentedCechColumn A q).obj.IsStrictlyGE a)
    (hB : ∀ q : Option SimplexCategory, (augmentedCechColumn B q).obj.IsStrictlyGE a) :
    ∃ R : CompatibleRoof Λ Y Y' h I I' A B,
      CanonicalRoofU Λ Y Y' h I I' A B η' R ∧
      CanonicalRoofV Λ Y Y' h I I' A B η R ∧
      R.w = (resolvedCechDiagram Λ Y' I').map b ∧
      CompatibleRoofColumnsGE Λ Y Y' h I I' A B a ∧
      (∀ q : Option SimplexCategory, QuasiIso (augmentedCechColumnMap R.v q)) ∧
      CompatibleRoofDerivedIdentification Λ Y Y' h I I' A B η η' b R := by
  sorry

end AlgebraicGeometry.Etale
