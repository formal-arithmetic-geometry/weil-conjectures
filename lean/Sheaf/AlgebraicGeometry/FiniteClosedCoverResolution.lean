/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.GroupTheory.Perm.Sign

import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates
import WeilConjectures.Algebra.Homology.FiniteStripAugmentation
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Finite closed-cover resolutions with the actual unit augmentation

Source: Stacks Project, proetale.tex, Tag 09AH (lemma-ses-associated-to-open),
and homology.tex, Tag 0133; finite-cover deduction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution)

Rows are specified by their graded terms and signed face maps. Units determine every
restriction, rather than an unspecified isomorphism class of a resolution. The finite
products used for the terms are canonically the finite direct sums in the abelian category.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry
noncomputable section

/-- The actual closed restriction endofunctor, inverse image followed by direct image.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedRestriction {X Z : Scheme.{u}} (i : Z ⟶ X) (A : Sheaf (ProEt.topology X)
  CommRingCat.{u + 1}) :=
  proEtaleModuleInverseImage i A ⋙ proEtaleRingedDirectImage i A

/-- Zero preservation inherited from the actual inverse-image/direct-image adjunction.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
instance finiteClosedRestriction_zero {X Z : Scheme.{u}} (i : Z ⟶ X) (A : Sheaf (ProEt.topology X)
  CommRingCat.{u + 1}) :
    (finiteClosedRestriction i A).PreservesZeroMorphisms :=
  letI := (ProEtaleClosedProjection.adjunction i A).isLeftAdjoint
  letI := (ProEtaleClosedProjection.adjunction i A).isRightAdjoint
  inferInstanceAs ((proEtaleModuleInverseImage i A ⋙ proEtaleRingedDirectImage i
    A).PreservesZeroMorphisms)

/-- The actual adjunction unit, normalized by the existing sectionwise construction.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedUnit {X Z : Scheme.{u}} (i : Z ⟶ X) (A : Sheaf (ProEt.topology X) CommRingCat.{u +
  1}) :
    𝟭 (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ⟶ finiteClosedRestriction i A :=
  (ProEtaleClosedProjection.adjunction i A).unit

/-- Scheme-theoretic intersection: the finite product in the category of schemes over X.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedIntersection {X : Scheme.{u}} {m : ℕ} (W : Fin m → Over X)
    (s : Finset (Fin m)) : Over X :=
  ∏ᶜ fun a : s ↦ W a.1

/-- Degree p terms, indexed by strictly increasing (p+1)-tuples. Finite products are biproducts.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedTerms {X : Scheme.{u}} {m : ℕ} (W : Fin m → Over X) (A : Sheaf (ProEt.topology X)
  CommRingCat.{u + 1})
    (p : ℕ) : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A) ⥤ ringedSiteModules.{u + 1}
      (proEtaleModuleCoefficients A) :=
  ∏ᶜ fun t : Fin (p + 1) ↪o Fin m ↦
    finiteClosedRestriction (finiteClosedIntersection W (Finset.univ.image t)).hom A

/-- Projection from a row term onto its indicated intersection factor.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedTermProjection {X : Scheme.{u}} {m : ℕ} (W : Fin m → Over X)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (p : ℕ)
    (t : Fin (p + 1) ↪o Fin m) : finiteClosedTerms W A p ⟶
      finiteClosedRestriction (finiteClosedIntersection W (Finset.univ.image t)).hom A :=
  Pi.π _ t

/-- Signed sum of face restrictions, with the sign of the deleted position.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedDifferential {X : Scheme.{u}} {m : ℕ}
    (W : Fin m → Over X) (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (r : ∀ s t : Finset (Fin m),
      finiteClosedRestriction (finiteClosedIntersection W s).hom A ⟶
        finiteClosedRestriction (finiteClosedIntersection W t).hom A)
    (p : ℕ) : finiteClosedTerms W A p ⟶ finiteClosedTerms W A (p + 1) :=
  Pi.lift fun t ↦ ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (Pi.π _ ((Fin.succAboveOrderEmb j).trans t) ≫
      r (Finset.univ.image ((Fin.succAboveOrderEmb j).trans t)) (Finset.univ.image t))

/-- The total exists by the existing coproducts of module sheaves.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
instance finiteClosedAllTotal {X : Scheme.{u}} (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (K : HomologicalComplex₂ (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    K.HasTotal (ComplexShape.up ℤ) := fun _ ↦ inferInstance

/-- Apply the additive row functor termwise and put horizontal degree first.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedDouble {X : Scheme.{u}} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (R : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A) ⥤ CochainComplex
      (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ) [R.Additive] :=
  R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- The ordinary direct-sum total, with differential d_horizontal + (-1)^p d_vertical.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedTotal {X : Scheme.{u}} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (R : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A) ⥤ CochainComplex
      (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ) [R.Additive] :=
  finiteClosedDouble R ⋙ HomologicalComplex₂.totalFunctor (ringedSiteModules.{u + 1}
    (proEtaleModuleCoefficients A))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- The unit-normalized augmented resolution. The terms and differential fix the entire
horizontal complex, including its vanishing outside columns 0,...,m-1. Unit equations fix
restrictions since the units onto closed restrictions are epimorphisms. The derived
isomorphism is exactly localization of the total augmentation, naturally on all bounded
below complexes. No data are chosen from this proposition in a definition.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
structure FiniteClosedResolution {X Z : Scheme.{u}} (i : Z ⟶ X) {m : ℕ}
    (W : Fin m → Over X) (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) where
  restriction : ∀ s t : Finset (Fin m),
    finiteClosedRestriction (finiteClosedIntersection W s).hom A ⟶
      finiteClosedRestriction (finiteClosedIntersection W t).hom A
  restriction_unit : ∀ (s t : Finset (Fin m)), s ⊆ t →
    finiteClosedUnit (finiteClosedIntersection W s).hom A ≫ restriction s t =
      finiteClosedUnit (finiteClosedIntersection W t).hom A
  restriction_zero : ∀ (s t : Finset (Fin m)), ¬s ⊆ t → restriction s t = 0
  rows : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A) ⥤ CochainComplex
    (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ
  additive : rows.Additive
  terms : ∀ p : ℕ, rows ⋙ HomologicalComplex.eval _ _ (p : ℤ) ≅ finiteClosedTerms W A p
  differential : ∀ (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) (p : ℕ),
    (terms p).inv.app M ≫ (rows.obj M).d (p : ℤ) ((p : ℤ) + 1) ≫
      (terms (p + 1)).hom.app M = (finiteClosedDifferential W A restriction p).app M
  support : ∀ (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) (p : ℤ), p < 0 ∨ (m :
    ℤ) ≤ p → IsZero ((rows.obj M).X p)
  augment : finiteClosedRestriction i A ⟶ rows ⋙ HomologicalComplex.eval _ _ (0 : ℤ)
  augment_unit : ∀ (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) (t : Fin 1 ↪o Fin
    m),
    (finiteClosedUnit i A).app M ≫ augment.app M ≫ (terms 0).hom.app M ≫
      (Pi.π (fun t : Fin 1 ↪o Fin m ↦
        finiteClosedRestriction (finiteClosedIntersection W (Finset.univ.image t)).hom A) t).app M =
        (finiteClosedUnit (finiteClosedIntersection W (Finset.univ.image t)).hom A).app M
  totalAugment : (finiteClosedRestriction i A).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
    @finiteClosedTotal X A rows additive
  totalAugment_f : ∀ (K : CochainComplex (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
    ℤ) (n : ℤ),
    (totalAugment.app K).f n = augment.app (K.X n) ≫
      ((@finiteClosedDouble X A rows additive).obj K).ιTotal (ComplexShape.up ℤ)
        0 n n (Int.zero_add n)
  quasiIso : ∀ (K : CochainComplex (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ),
    CochainComplex.plus _ K →
    QuasiIso (totalAugment.app K)
  derivedIso : CochainComplex.Plus.ι (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ⋙
      (finiteClosedRestriction i A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ≅
    CochainComplex.Plus.ι (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ⋙
      @finiteClosedTotal X A rows additive ⋙ DerivedCategory.Q
  derivedIso_hom : ∀ K : CochainComplex.Plus (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients
    A)),
    derivedIso.hom.app K = DerivedCategory.Q.map (totalAugment.app K.obj)

/-- The unique augmentation-compatible derived comparison between two resolutions.
Its formula proves independence of refinement functions and compatibility with composition.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedDerivedRefinement {X Z : Scheme.{u}} {i : Z ⟶ X} {m n : ℕ}
    {W : Fin m → Over X} {V : Fin n → Over X} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (D : FiniteClosedResolution i W A) (D' : FiniteClosedResolution i V A) :
    CochainComplex.Plus.ι (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ⋙
        @finiteClosedTotal X A D.rows D.additive ⋙ DerivedCategory.Q ≅
      CochainComplex.Plus.ι (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ⋙
        @finiteClosedTotal X A D'.rows D'.additive ⋙ DerivedCategory.Q :=
  D.derivedIso.symm ≪≫ D'.derivedIso

/-- The alternating sign of a tuple under a refinement function. Repeated images have
coefficient zero; otherwise the unique sorting permutation supplies its sign.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedRefinementSign {m n p : ℕ} (f : Fin n → Fin m)
    (s : Fin (p + 1) ↪o Fin m) (t : Fin (p + 1) ↪o Fin n) : ℤ :=
  ∑ σ : Equiv.Perm (Fin (p + 1)),
    if ∀ k, s (σ k) = f (t k) then (Equiv.Perm.sign σ : ℤ) else 0

/-- The signed component formula for a refinement, using the actual restriction maps.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedRefinementMap {X : Scheme.{u}} {m n : ℕ}
    (W : Fin m → Over X) (V : Fin n → Over X) (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (f
      : Fin n → Fin m)
    (c : ∀ (s : Finset (Fin m)) (t : Finset (Fin n)),
      finiteClosedRestriction (finiteClosedIntersection W s).hom A ⟶
        finiteClosedRestriction (finiteClosedIntersection V t).hom A)
    (p : ℕ) : finiteClosedTerms W A p ⟶ finiteClosedTerms V A p :=
  Pi.lift fun t ↦ ∑ s : Fin (p + 1) ↪o Fin m,
    finiteClosedRefinementSign f s t •
      (Pi.π _ s ≫ c (Finset.univ.image s) (Finset.univ.image t))

/-- Termwise application and totalization of a natural morphism of row complexes.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedTotalMap {X Z : Scheme.{u}} {i : Z ⟶ X} {m n : ℕ}
    {W : Fin m → Over X} {V : Fin n → Over X} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (D : FiniteClosedResolution i W A) (D' : FiniteClosedResolution i V A)
    (ρ : D.rows ⟶ D'.rows) :
    @finiteClosedTotal X A D.rows D.additive ⟶
      @finiteClosedTotal X A D'.rows D'.additive :=
  letI := D.additive
  letI := D'.additive
  Functor.whiskerRight
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ))
      (HomologicalComplex₂.flipFunctor (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)))
    (HomologicalComplex₂.totalFunctor (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- Refinements lift to the specified signed row map and preserve the augmentation.
The derived map is the augmentation-normalized comparison; hence it is independent of
choices of refinement function and is compatible with iterated refinements.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def FiniteClosedRefinementCompatible {X Z : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (D :
      FiniteClosedResolution i W A) : Prop :=
  ∀ (n : ℕ) (_hn : 0 < n) (V : Fin n → Over X)
    (_hclosed : ∀ b, IsClosedImmersion (V b).hom)
    (_hcover : Set.range i = ⋃ b, Set.range (V b).hom)
    (_hqc : ∀ b, ∃ U : X.Opens,
      Set.range U.ι = (Set.range (V b).hom)ᶜ ∧ QuasiCompact U.ι)
    (f : Fin n → Fin m) (_hf : ∀ b, Nonempty (V b ⟶ W (f b)))
    (D' : FiniteClosedResolution i V A),
    ∃ c : ∀ (s : Finset (Fin m)) (t : Finset (Fin n)),
        finiteClosedRestriction (finiteClosedIntersection W s).hom A ⟶
          finiteClosedRestriction (finiteClosedIntersection V t).hom A,
      (∀ (s : Finset (Fin m)) (t : Finset (Fin n)), s ⊆ t.image f →
        finiteClosedUnit (finiteClosedIntersection W s).hom A ≫ c s t =
          finiteClosedUnit (finiteClosedIntersection V t).hom A) ∧
      (∀ (s : Finset (Fin m)) (t : Finset (Fin n)), ¬s ⊆ t.image f → c s t = 0) ∧
      ∃ ρ : D.rows ⟶ D'.rows,
        (∀ (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) (p : ℕ),
          (D.terms p).inv.app M ≫ (ρ.app M).f (p : ℤ) ≫ (D'.terms p).hom.app M =
            (finiteClosedRefinementMap W V A f c p).app M) ∧
        D.totalAugment ≫ finiteClosedTotalMap D D' ρ = D'.totalAugment ∧
        ∀ K : CochainComplex.Plus (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)),
          DerivedCategory.Q.map ((finiteClosedTotalMap D D' ρ).app K.obj) =
            (finiteClosedDerivedRefinement D D').hom.app K

/-- Inverse image preserves zero maps, as a left adjoint between module categories.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
instance finiteClosedInverseZero {X Y : Scheme.{u}} (g : Y ⟶ X) (A : Sheaf (ProEt.topology X)
  CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage g A).PreservesZeroMorphisms :=
  letI := (ProEtaleClosedProjection.adjunction g A).isLeftAdjoint
  inferInstanceAs ((proEtaleModuleInverseImage g A).PreservesZeroMorphisms)

/-- The recorded module inverse image applied termwise, with inverse-image coefficients.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedPullbackComplex {X Y : Scheme.{u}} (g : Y ⟶ X) (A : Sheaf (ProEt.topology X)
  CommRingCat.{u + 1}) :=
  (proEtaleModuleInverseImage g A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ordered closed family after scheme-theoretic base change.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedPullbackFamily {X Y : Scheme.{u}} {m : ℕ}
    (W : Fin m → Over X) (g : Y ⟶ X) : Fin m → Over Y :=
  fun a ↦ Over.mk (pullback.fst g (W a).hom)

/-- The product-of-intersection-comparisons formula for a pullback row map.
It specifies the map by all product projections, avoiding a choice of a product isomorphism.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def finiteClosedPullbackRowFormula {X Z Y : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (D : FiniteClosedResolution i W A) (g : Y ⟶ X)
    (D' : FiniteClosedResolution (pullback.fst g i) (finiteClosedPullbackFamily W g)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj A))
    (cs : ∀ s : Finset (Fin m),
      finiteClosedRestriction (finiteClosedIntersection W s).hom A ⋙
          proEtaleModuleInverseImage g A ≅
        proEtaleModuleInverseImage g A ⋙
          finiteClosedRestriction (finiteClosedIntersection (finiteClosedPullbackFamily W g) s).hom
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj A))
    (σ : D.rows ⋙ finiteClosedPullbackComplex g A ⟶ proEtaleModuleInverseImage g A ⋙ D'.rows) :
    Prop :=
  ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin m),
    Functor.whiskerRight σ (HomologicalComplex.eval _ _ (p : ℤ)) ≫
        Functor.whiskerLeft (proEtaleModuleInverseImage g A)
          ((D'.terms p).hom ≫
            finiteClosedTermProjection (finiteClosedPullbackFamily W g)
              ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj A) p t) =
      Functor.whiskerRight
          ((D.terms p).hom ≫ finiteClosedTermProjection W A p t)
          (proEtaleModuleInverseImage g A) ≫ (cs (Finset.univ.image t)).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback compatibility on every intersection, on rows, and on their finite totals.
The row map has exactly the product of the supplied unit-compatible comparisons as its
components. The equation on diagonal inclusions specifies its totalization through the
canonical interchange g* Tot ≅ Tot g*: it sends each g*(p,q)-summand by σ in degree p
into the target (p,q)-summand. Thus τ is the actual totalized row map, not an arbitrary
augmentation-compatible map. Its localization is the unique augmentation-normalized
derived comparison e. All equations are natural in the module or complex and remain so
after whiskering by any parameter diagram.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: lem-sfb-finite-closed-cover-resolution). -/
def FiniteClosedPullbackCompatible {X Z : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (D : FiniteClosedResolution i W A) : Prop :=
  ∀ {Y : Scheme.{u}} (g : Y ⟶ X)
    (D' : FiniteClosedResolution (pullback.fst g i) (finiteClosedPullbackFamily W g)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj A))
    (c : finiteClosedRestriction i A ⋙ proEtaleModuleInverseImage g A ≅
      proEtaleModuleInverseImage g A ⋙ finiteClosedRestriction (pullback.fst g i)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj A))
    (_hc : ∀ M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A),
      (proEtaleModuleInverseImage g A).map ((finiteClosedUnit i A).app M) ≫ c.hom.app M =
        (finiteClosedUnit (pullback.fst g i)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj A)).app
            ((proEtaleModuleInverseImage g A).obj M))
    (cs : ∀ s : Finset (Fin m),
      finiteClosedRestriction (finiteClosedIntersection W s).hom A ⋙
          proEtaleModuleInverseImage g A ≅
        proEtaleModuleInverseImage g A ⋙
          finiteClosedRestriction (finiteClosedIntersection (finiteClosedPullbackFamily W g) s).hom
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj A))
    (_hcs : ∀ (s : Finset (Fin m))
      (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)),
      (proEtaleModuleInverseImage g A).map
          ((finiteClosedUnit (finiteClosedIntersection W s).hom A).app M) ≫
        (cs s).hom.app M =
          (finiteClosedUnit (finiteClosedIntersection (finiteClosedPullbackFamily W g) s).hom
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj A)).app
              ((proEtaleModuleInverseImage g A).obj M)),
    ∃ σ : D.rows ⋙ finiteClosedPullbackComplex g A ⟶ proEtaleModuleInverseImage g A ⋙ D'.rows,
      finiteClosedPullbackRowFormula D g D' cs σ ∧
      (∀ M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A),
        (proEtaleModuleInverseImage g A).map (D.augment.app M) ≫ (σ.app M).f 0 =
          c.hom.app M ≫ D'.augment.app ((proEtaleModuleInverseImage g A).obj M)) ∧
      ∃ τ : @finiteClosedTotal X A D.rows D.additive ⋙ finiteClosedPullbackComplex g A ⟶
          finiteClosedPullbackComplex g A ⋙
            @finiteClosedTotal Y _ D'.rows D'.additive,
        (∀ (K : CochainComplex
          (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ)
          (p q n : ℤ) (h : p + q = n),
          (proEtaleModuleInverseImage g A).map
              (((@finiteClosedDouble X A D.rows D.additive).obj K).ιTotal
                (ComplexShape.up ℤ) p q n h) ≫ (τ.app K).f n =
            (σ.app (K.X q)).f p ≫
              (((@finiteClosedDouble Y _ D'.rows D'.additive).obj
                ((finiteClosedPullbackComplex g A).obj K)).ιTotal
                  (ComplexShape.up ℤ) p q n h)) ∧
        ∃! e : CochainComplex.Plus.ι
              (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ⋙
            @finiteClosedTotal X A D.rows D.additive ⋙
              finiteClosedPullbackComplex g A ⋙ DerivedCategory.Q ≅
          CochainComplex.Plus.ι
              (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ⋙
            finiteClosedPullbackComplex g A ⋙
              @finiteClosedTotal Y _ D'.rows D'.additive ⋙ DerivedCategory.Q,
          (∀ K : CochainComplex.Plus
            (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)),
            DerivedCategory.Q.map
                ((finiteClosedPullbackComplex g A).map (D.totalAugment.app K.obj)) ≫
              e.hom.app K =
                DerivedCategory.Q.map
                  (((c.hom.mapHomologicalComplex (ComplexShape.up ℤ)).app K.obj)) ≫
                DerivedCategory.Q.map (D'.totalAugment.app
                  ((finiteClosedPullbackComplex g A).obj K.obj))) ∧
          (∀ K : CochainComplex.Plus
            (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)),
            DerivedCategory.Q.map (τ.app K.obj) = e.hom.app K)

/-- Finite closed-cover resolution, naturally augmented by the actual restriction units.

Source: Stacks Project, proetale.tex, Tag 09AH, and homology.tex, Tag 0133;
finite-cover deduction (blueprint: lem-sfb-finite-closed-cover-resolution).

Proof: (1) Closed immersions and quasi-compact complementary opens remain so after base
change. Complements of intersections are finite unions of these quasi-compact opens.
The ringed open-closed localization sequence and exact inverse image show each closed
restriction is exact. (2) Form the displayed finite products of closed restrictions.
For an inclusion of intersections use the pushed-forward actual adjunction unit with
its inverse-image compositor. The composite-unit identity gives restriction composition
and the displayed augmentation equation. In d squared, each pair of deletions occurs
with opposite signs and identical restrictions. This gives the additive row functor.
(3) Zero detection follows by induction on the number of closed members: localization
at the first member identifies a module vanishing there with extension by zero from its
complement, where induction applies. For zero members the remaining support is empty.
(4) Exactness is Zariski local, since open restriction is exact and commutes with closed
direct image. On affine charts all schemes in the closed base-change squares are qcqs,
so lem-sf-ring-sheaf-base-change-mates identifies restriction to each closed member with
the corresponding intersection complex, including its units. (5) Insert that member's
index with sign (-1) to the number of preceding indices, using the inverse of the
restriction which becomes an identity intersection. Deletion-insertion cancellation
gives dh+hd=1, including degree -1 and the last degree. The restricted row is exact.
(6) Off Z all terms vanish. Apply exact inverse image to row homology and use step 3
to conclude its vanishing. Thus each module-row augmentation is a quasi-isomorphism.
(7) Apply the construction termwise. The finitely many columns have finite diagonals;
lem-sc-finite-strip-row-augmentation proves that the specified total augmentation is a
quasi-isomorphism. Localization gives its natural derived isomorphism. (8) A refinement
restricts tuples, assigning zero to repeated images and the sorting sign otherwise.
The deletion formulas verify the chain equation; for repeated indices the only two
remaining terms cancel. Composite units give its augmentation equation. In the derived
category this determines it uniquely, proving independence and composition. Exact inverse
image and unit-compatible comparisons for every intersection identify the face maps:
precomposing both candidate restrictions with the epimorphic closed unit gives the same
unit. Taking products gives σ, whose components are exactly these comparisons; the
singleton unit equations similarly give its augmentation square. Exact inverse image
preserves the finite sums on each diagonal. The canonical interchange with totalization
therefore totalizes σ to τ, characterized by the displayed diagonal-inclusion equation.
The augmentation square persists under totalization, so localization of τ is precisely
the comparison determined by the source comparison and the invertible augmentations.
These are natural-transformation identities, so they hold for all diagram
automorphisms and parameter diagrams, not just parameter points. -/
theorem finite_closed_cover_resolution {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (m : ℕ) (hm : 0 < m) (W : Fin m → Over X)
    (hclosed : ∀ a, IsClosedImmersion (W a).hom)
    (hfactor : ∀ a, Nonempty (W a ⟶ Over.mk i))
    (hcover : Set.range i = ⋃ a, Set.range (W a).hom)
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (hqcW : ∀ a, ∃ U : X.Opens,
      Set.range U.ι = (Set.range (W a).hom)ᶜ ∧ QuasiCompact U.ι)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) : ∃ D : FiniteClosedResolution i W A,
      FiniteClosedRefinementCompatible D ∧ FiniteClosedPullbackCompatible D := by
  sorry
end
end AlgebraicGeometry
