/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.TraceFormula.SiteAugmentationAcyclicCech
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.CanonicalFiltration

import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.TraceFormula.TotalSiteComponentRestriction
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.CategoryTheory.SliceSiteSimplicialAugmentation
import Sheaf.TraceFormula.TotalSiteInjectiveAugmentationExactness

/-!
# Augmentation spectral sequence for a total simplicial site

Source: Stacks Project, spaces-simplicial.tex, Tags 09WL, 0D79 and 0D7A
(blueprint: lem-trf-site-augmentation-spectral-sequence).

We reuse the actual comma total site and its vertical topology, the slice
localizations, the counit edge, and Mathlib's alternating coface complex.
The derived direct image is the right derived functor on bounded below
categories, evaluated on a sheaf placed in degree zero.

## Main definitions

* `HasAugmentationPageOne`: actual derived component terms and alternating d1.
* `IsAugmentationResolutionComparison`: the canonical comparison via j and rho.
* `HasAugmentationConvergence`: finite natural convergence and the bottom edge.
* `HasAugmentationSpectralSequence`: the complete augmentation assertion.

## Main statement

* `site_augmentation_spectral_sequence`: existence for every augmented simplicial site.
-/

@[expose] public noncomputable section

universe u v w w' uA vA uF vF

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SimplicialSlice

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- The component direct-image functor is precomposition on abelian sheaves,
so its action on morphisms preserves addition definitionally. Source: Stacks,
Tag 0D79 (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
instance componentDirectAdditive (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) (p : SimplexCategory) :
    (componentDirect J A p).Additive where
  map_add := rfl

/-- Evaluation of an actual page of a first-quadrant spectral sequence.
Source: Stacks, Tag 0132 (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def augmentationPageTermFunctor {B : Type uA} [Category.{vA} B] [Abelian B]
    (r : ℤ) (hr : 1 ≤ r) (pq : ℕ × ℕ) :
    CohomologicalSpectralSequenceNat B 1 ⥤ B :=
  SpectralSequence.pageFunctor B _ 1 r hr ⋙ HomologicalComplex.eval B _ pq

/-- Restrict from E1 to E2, keeping the actual pages and homology
identifications. Source: Stacks, Homology, Tag 0132
(blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def augmentationPagesFromTwo {B : Type uA} [Category.{vA} B] [Abelian B]
    (E : CohomologicalSpectralSequenceNat B 1) : E₂CohomologicalSpectralSequenceNat B where
  page r hr := E.page r (by omega)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (by omega)

/-- The genuine bottom edge: successive page maps are the homology
quotients, and the stable term is included through the abutment filtration.
Source: Stacks, Homology, Tags 012W and 0132, and Tag 0D7A
(blueprint: lem-trf-site-augmentation-spectral-sequence). -/
structure AugmentationBottomEdge {B : Type uA} [Category.{vA} B] [Abelian B]
    (E : CohomologicalSpectralSequenceNat B 1) (T H : ℕ → B)
    (bottomRow : ∀ p : ℕ, T p ≅ (E.page 2 (by decide)).X (p, 0))
    (abutment : (augmentationPagesFromTwo E).Abutment H)
    (gradedIso : ∀ p : ℕ,
      cokernel (Subobject.ofLE _ _ (abutment.filtration_succ_le p p)) ≅
        (E.page ((p + 2 : ℕ) : ℤ) (by omega)).X (p, 0))
    (edge : ∀ p : ℕ, T p ⟶ H p) where
  passage : ∀ p r : ℕ,
    (E.page ((r + 2 : ℕ) : ℤ) (by omega)).X (p, 0) ⟶
      (E.page ((r + 3 : ℕ) : ℤ) (by omega)).X (p, 0)
  passage_eq : ∀ p r : ℕ,
    (E.page ((r + 2 : ℕ) : ℤ) (by omega)).iCycles (p, 0) ≫ passage p r =
      (E.page ((r + 2 : ℕ) : ℤ) (by omega)).homologyπ (p, 0) ≫
        (E.iso ((r + 2 : ℕ) : ℤ) ((r + 3 : ℕ) : ℤ) (p, 0)
          (by omega) (by omega)).hom
  iterate : ∀ p r : ℕ, T p ⟶
    (E.page ((r + 2 : ℕ) : ℤ) (by omega)).X (p, 0)
  iterate_zero : ∀ p : ℕ, iterate p 0 = (bottomRow p).hom
  iterate_succ : ∀ p r : ℕ, iterate p (r + 1) = iterate p r ≫ passage p r
  stableFactor : ∀ p : ℕ,
    (E.page ((p + 2 : ℕ) : ℤ) (by omega)).X (p, 0) ⟶
      (abutment.filtration p p : B)
  stableFactor_isIso : ∀ p : ℕ, IsIso (stableFactor p)
  stableFactor_eq : ∀ p : ℕ,
    cokernel.π (Subobject.ofLE _ _ (abutment.filtration_succ_le p p)) ≫
        (gradedIso p).hom ≫ stableFactor p =
      𝟙 (abutment.filtration p p : B)
  edge_eq : ∀ p : ℕ,
    edge p = iterate p p ≫ stableFactor p ≫ (abutment.filtration p p).arrow

/-- Naturality of a finite abutment includes both its subobjects and its
specified associated-graded identifications. Source: Stacks, Tag 0132 and
Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
structure AugmentationNaturalAbutment {D : Type uF} [Category.{vF} D]
    {B : Type uA} [Category.{vA} B] [Abelian B]
    (E : D ⥤ CohomologicalSpectralSequenceNat B 1) (H : ℕ → D ⥤ B)
    (a : ∀ F : D, (augmentationPagesFromTwo (E.obj F)).Abutment
      (fun n : ℕ ↦ (H n).obj F))
    (gradedIso : ∀ (F : D) (n p q : ℕ) (_hpq : p + q = n),
      cokernel (Subobject.ofLE _ _ ((a F).filtration_succ_le n p)) ≅
        (augmentationPagesFromTwo (E.obj F)).pageInfinity (p, q)) where
  filtrationMap : ∀ {F G : D} (_φ : F ⟶ G) (n p : ℕ),
    ((a F).filtration n p : B) ⟶ ((a G).filtration n p : B)
  filtrationMap_comm : ∀ {F G : D} (φ : F ⟶ G) (n p : ℕ),
    filtrationMap φ n p ≫ ((a G).filtration n p).arrow =
      ((a F).filtration n p).arrow ≫ (H n).map φ
  graded_naturality : ∀ {F G : D} (φ : F ⟶ G) (n p q : ℕ) (hpq : p + q = n),
    ∃ ψ : cokernel (Subobject.ofLE _ _ ((a F).filtration_succ_le n p)) ⟶
        cokernel (Subobject.ofLE _ _ ((a G).filtration_succ_le n p)),
      cokernel.π (Subobject.ofLE _ _ ((a F).filtration_succ_le n p)) ≫ ψ =
        filtrationMap φ n p ≫
          cokernel.π (Subobject.ofLE _ _ ((a G).filtration_succ_le n p)) ∧
      ψ ≫ (gradedIso G n p q hpq).hom =
        (gradedIso F n p q hpq).hom ≫
          ((E.map φ).hom ((p + q + 2 : ℕ) : ℤ) (by omega)).f (p, q)

variable (J : GrothendieckTopology C) (A : SimplicialObject.Augmented C)
    [HasDerivedCategory.{w'} (AbelianSheaf J A.left)]
    [HasDerivedCategory.{w} (Sheaf (J.over A.right) AddCommGrpCat.{max u v})]

/-- The actual derived direct image of sheaves placed in degree zero.
Source: Stacks, Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def augmentationDerivedDirect : AbelianSheaf J A.left ⥤
    DerivedCategory.Plus (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) :=
  DerivedCategory.Plus.singleFunctor (AbelianSheaf J A.left) 0 ⋙
    (direct J A).rightDerivedFunctorPlus

/-- The abutment cohomology functor in degree n. Source: Stacks, Tag 0D7A
(blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def augmentationCohomology (n : ℕ) : AbelianSheaf J A.left ⥤
    Sheaf (J.over A.right) AddCommGrpCat.{max u v} :=
  augmentationDerivedDirect J A ⋙
    DerivedCategory.Plus.homologyFunctor
      (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) (n : ℤ)

/-- The cohomology of the actual alternating-face complex. Source: Stacks,
Tag 0D79 (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def augmentationCechCohomology (n : ℕ) : AbelianSheaf J A.left ⥤
    Sheaf (J.over A.right) AddCommGrpCat.{max u v} :=
  cechDerivedFunctor J A ⋙
    DerivedCategory.Plus.homologyFunctor
      (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) (n : ℤ)

/-- Extend a nonnegative complex by zero as a bounded below complex.
Source: Stacks, Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def augmentationNonnegativePlus {B : Type uA} [Category.{vA} B] [Abelian B] :
    CochainComplex B ℕ ⥤ CochainComplex.Plus B where
  obj K := ⟨K.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  map f := ObjectProperty.homMk
    ((ComplexShape.embeddingUpNat.extendFunctor B).map f)

/-- The alternating coface functor acts additively on sheaf morphisms.
Source: Stacks, Tag 0D79 (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
instance augmentationCechAdditive : (cechFunctor J A).Additive where
  map_add := rfl

/-- The genuine resolution bicomplex bp,* Ip^q, with face degree first.
Source: Stacks, Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def augmentationResolutionBicomplex (F : AbelianSheaf J A.left) :
    HomologicalComplex₂ (Sheaf (J.over A.right) AddCommGrpCat.{max u v})
      (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  HomologicalComplex₂.flip
    (((cechFunctor J A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution F).cocomplex)

/-- The pushforward of the chosen resolution, before localization.
Source: Stacks, Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def augmentationResolutionDirect (F : AbelianSheaf J A.left) :
    CochainComplex (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) ℕ :=
  ((direct J A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution F).cocomplex

/-- Canonical computation of Rb,*F by b,*I, including extension by zero.
Source: Stacks, Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def augmentationResolutionDerivedIso (F : AbelianSheaf J A.left) :
    (augmentationDerivedDirect J A).obj F ≅
      (augmentationNonnegativePlus ⋙ DerivedCategory.Plus.Q).obj
        (augmentationResolutionDirect J A F) :=
  (direct J A).rightDerivedFunctorPlusObjSingleFunctorIsoQ F ≪≫
    DerivedCategory.Plus.Q.mapIso (ObjectProperty.isoMk _
      ((injectiveResolution F).cocomplex.mapExtendIso
        ComplexShape.embeddingUpNat (direct J A)))

/-- The comparison is exactly rho inverse times j for the chosen injective
resolution. Its components are the canonical coaugmentation and the counit edge.
Source: Stacks, Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def IsAugmentationResolutionComparison
    (comparison : cechDerivedFunctor J A ⟶ augmentationDerivedDirect J A) : Prop :=
  ∀ F : AbelianSheaf J A.left,
  ∃ (j : (cechFunctor J A).obj F ⟶
        (augmentationResolutionBicomplex J A F).total (ComplexShape.up ℕ))
    (ρ : augmentationResolutionDirect J A F ⟶
        (augmentationResolutionBicomplex J A F).total (ComplexShape.up ℕ)),
    QuasiIso ρ ∧
    (∀ p : ℕ, j.f p =
      (componentDirect J A (SimplexCategory.mk p)).map
          ((injectiveResolution F).ι.f 0) ≫
        (augmentationResolutionBicomplex J A F).ιTotal (ComplexShape.up ℕ)
          p 0 p (by simp)) ∧
    (∀ q : ℕ, ρ.f q = edge J A ((injectiveResolution F).cocomplex.X q) ≫
      (augmentationResolutionBicomplex J A F).ιTotal (ComplexShape.up ℕ)
        0 q q (by simp)) ∧
    comparison.app F ≫ (augmentationResolutionDerivedIso J A F).hom ≫
        (augmentationNonnegativePlus ⋙ DerivedCategory.Plus.Q).map ρ =
      (augmentationNonnegativePlus ⋙ DerivedCategory.Plus.Q).map j

/-- The derived coface is induced by the canonical transition mate on sheaves.
Source: Stacks, Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def augmentationDerivedCoface (p q : ℕ) (i : Fin (p + 2)) :
    (componentDirect J A (SimplexCategory.mk p)).rightDerived q ⟶
      (componentDirect J A (SimplexCategory.mk (p + 1))).rightDerived q :=
  NatTrans.rightDerived
    (F := componentDirect J A (SimplexCategory.mk p))
    (G := componentDirect J A (SimplexCategory.mk (p + 1)))
    (componentDirectMap J A (p := SimplexCategory.mk p)
      (q := SimplexCategory.mk (p + 1)) (SimplexCategory.δ i)) q

/-- The E1 terms and alternating d1 are those of the actual component direct
images, naturally in the coefficient sheaf. Source: Stacks, Tag 0D7A
(blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def HasAugmentationPageOne
    (spectral : AbelianSheaf J A.left ⥤ CohomologicalSpectralSequenceNat
      (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) 1) : Prop :=
  ∃ pageOne : ∀ p q : ℕ,
      spectral ⋙ augmentationPageTermFunctor 1 (by decide) (p, q) ≅
        (componentDirect J A (SimplexCategory.mk p)).rightDerived q,
    (∀ p q : ℕ, Nonempty (
      (componentDirect J A (SimplexCategory.mk p)).rightDerived q ≅
        restriction J A.left (op (SimplexCategory.mk p)) ⋙
          (localizationDirect J A (op (SimplexCategory.mk p))).rightDerived q)) ∧
    ∀ (F : AbelianSheaf J A.left) (p q : ℕ),
      ((spectral.obj F).page 1 (by decide)).d (p, q) (p + 1, q) ≫
          (pageOne (p + 1) q).hom.app F =
        (pageOne p q).hom.app F ≫
          ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
            (augmentationDerivedCoface J A p q i).app F

/-- Finite natural convergence, with specified associated-graded isomorphisms
and bottom edge equal to homology of the canonical comparison. Source: Stacks,
Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def HasAugmentationConvergence
    (spectral : AbelianSheaf J A.left ⥤ CohomologicalSpectralSequenceNat
      (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) 1)
    (comparison : cechDerivedFunctor J A ⟶ augmentationDerivedDirect J A) : Prop :=
  ∃ bottomRow : ∀ p : ℕ,
      augmentationCechCohomology J A p ≅
        spectral ⋙ augmentationPageTermFunctor 2 (by decide) (p, 0),
  ∃ abutment : ∀ F : AbelianSheaf J A.left,
      (augmentationPagesFromTwo (spectral.obj F)).Abutment
        (fun n : ℕ ↦ (augmentationCohomology J A n).obj F),
  ∃ gradedIso : ∀ (F : AbelianSheaf J A.left) (n p q : ℕ) (_hpq : p + q = n),
      cokernel (Subobject.ofLE _ _ ((abutment F).filtration_succ_le n p)) ≅
        (augmentationPagesFromTwo (spectral.obj F)).pageInfinity (p, q),
    Nonempty (AugmentationNaturalAbutment spectral
      (augmentationCohomology J A) abutment gradedIso) ∧
    ∀ F : AbelianSheaf J A.left,
      Nonempty (AugmentationBottomEdge (spectral.obj F)
        (fun n : ℕ ↦ (augmentationCechCohomology J A n).obj F)
        (fun n : ℕ ↦ (augmentationCohomology J A n).obj F)
        (fun p : ℕ ↦ (bottomRow p).app F) (abutment F)
        (fun p : ℕ ↦ gradedIso F p p 0 (by simp))
        (fun p : ℕ ↦
          (DerivedCategory.Plus.homologyFunctor
            (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) (p : ℤ)).map
              (comparison.app F)))

/-- A natural augmentation spectral sequence on the actual total slice site.
Source: Stacks, Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence). -/
def HasAugmentationSpectralSequence : Prop :=
  ∃ spectral : AbelianSheaf J A.left ⥤ CohomologicalSpectralSequenceNat
      (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) 1,
  ∃ comparison : cechDerivedFunctor J A ⟶ augmentationDerivedDirect J A,
    HasAugmentationPageOne J A spectral ∧
    IsAugmentationResolutionComparison J A comparison ∧
    HasAugmentationConvergence J A spectral comparison ∧
    ∀ F : AbelianSheaf J A.left,
      edgeH0 J A F ≫
          (DerivedCategory.Plus.homologyFunctor _ 0).map (comparison.app F) =
        (direct J A).rightDerivedPlusSingleUnitHomology F

/-- The augmentation spectral sequence for every sheaf on the total slice site.

Source: Stacks, Tag 0D7A (blueprint: lem-trf-site-augmentation-spectral-sequence).
Proof:
1. Abelian sheaves on these small sites are Grothendieck and have enough injectives
   (lem-weil-pbc-site-sheaves-enough-injectives,
   lem-weil-pbc-ring-sheaves-grothendieck). Choose the nonnegative injective
   resolution I of F. Its direct image computes Rb,*F by
   lem-weil-pbc-right-derived-plus-injective. Component restriction is exact and
   preserves injectives (lem-trf-total-site-component-restriction), so the columns
   bp,* Ip compute Rq bp,* Fp, naturally in the cofaces.
2. Form the actual first-quadrant bicomplex with horizontal alternating cofaces
   and total sign dh + (-1)^p dv (def-sp-double-complex-total). The rows augmented
   by b,* Iq are exact (lem-trf-total-site-injective-augmentation-exactness).
   Their counit maps define rho, which is a quasi-isomorphism by
   lem-sc-first-quadrant-column-augmentation.
3. Its first spectral sequence gives E1 and d1 as stated and the finite
   filtration of Hn(Tot), transported through rho to Hn(Rb,*F)
   (thm-sp-double-complex-spectral-sequences). Left exactness identifies the
   bottom E1 row with Cb(F), hence E2 with its cohomology.
4. The resolution augmentation induces j by the (p,0) total inclusions.
   Define kappa by rho inverse times j using the canonical derived computation.
   The bottom-row quotient maps to the stable page, then its filtration
   inclusion, represent exactly the same cocycle in the total complex. This
   proves the asserted bottom-edge equation with the specified graded isomorphisms.
5. K-injective resolution comparisons are unique up to homotopy
   (lem-sp-kinjective-computes, lem-weil-pbc-kinjective-hom-derived).
   The induced total homotopy has sign (-1)^p in face degree p; its horizontal
   cross terms cancel. It preserves the filtration and induces vertical
   homotopies, giving identical E1 and subsequent maps. Identity and composition
   comparisons give naturality of the spectral sequence, its finite abutment
   and its specified graded identifications, and of kappa.
6. The actual counit edge is a cycle by the two cofaces' compatibility
   (lem-trf-slice-site-simplicial-augmentation and Tag 0D79). In total degree zero
   counit naturality gives j e = rho b,* i. Taking H0 and composing with
   H0(rho) inverse gives exactly H0(kappa) e = the canonical derived-unit
   identification, as left exactness identifies b,*F with H0(b,*I). -/
theorem site_augmentation_spectral_sequence
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (J : GrothendieckTopology C) (A : SimplicialObject.Augmented C)
    [HasDerivedCategory.{w'} (AbelianSheaf J A.left)]
    [HasDerivedCategory.{w} (Sheaf (J.over A.right) AddCommGrpCat.{max u v})] :
    HasAugmentationSpectralSequence J A := by
  sorry

end CategoryTheory.SimplicialSlice
