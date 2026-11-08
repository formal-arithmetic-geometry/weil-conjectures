/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionDerivedTensorComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionTotalComparison
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Hom
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Submission.WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import Submission.WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import Submission.WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
public import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Submission.WeilConjectures.CategoryTheory.SheafTensor
public import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import Submission.WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Submission.WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Submission.WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationTranspose
public import Submission.WeilConjectures.AlgebraicGeometry.InternalSliceDerivedHomComparison

import Submission.WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import Mathlib.Algebra.Ring.Ext

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Module objects and derived Hom on a slice

Source: Stacks Project, Tags 03DH, 08J9 and 08JB; Step 5 of the module-object
comparison (blueprint: def-sfb-internal-slice-derived-hom-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule CategoryTheory.MonObj WeilConjectures
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

attribute [local instance 1000001] sectionRingHasSheafCompose
attribute [local instance] sectionFunctorAdditiveForSite sectionFunctorEquivalenceForSite
-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃

/-- The tensor-Hom evaluation comparison, written once with abstract category endpoints.
Source: Stacks 08J9 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def homEvaluationSquare
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    (t : C × C ⥤ C) (h : Cᵒᵖ × C ⥤ C)
    (ev : ∀ K N : C, t.obj (h.obj (op K, N), K) ⟶ N)
    (f : C ⥤ D) (s : D × D ⥤ D) (H : Dᵒᵖ × D ⥤ D)
    (Ev : ∀ K N : D, s.obj (H.obj (op K, N), K) ⟶ N)
    (tensorIso : t ⋙ f ≅ (f.prod f) ⋙ s)
    (homIso : h ⋙ f ≅ (f.op.prod f) ⋙ H) : Prop :=
  ∀ K N : C,
    f.map (ev K N) = tensorIso.hom.app (h.obj (op K, N), K) ≫
      s.map (X := (f.obj (h.obj (op K, N)), f.obj K))
        (Y := (H.obj (op (f.obj K), f.obj N), f.obj K))
        (homIso.hom.app (op K, N), 𝟙 (f.obj K)) ≫ Ev (f.obj K) (f.obj N)

/-- The restriction square with its section-comparison isomorphisms in both Hom slots.
Source: Stacks 08JB, Step 5
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def homRestrictionSquare
    {C : Type u₀} [Category.{v₀} C] {E : Type u₁} [Category.{v₁} E]
    {D : Type u₂} [Category.{v₂} D] {F : Type u₃} [Category.{v₃} F]
    (h : Cᵒᵖ × C ⥤ C) (hu : Eᵒᵖ × E ⥤ E)
    (H : Dᵒᵖ × D ⥤ D) (HU : Fᵒᵖ × F ⥤ F)
    (e : C ⥤ D) (eu : E ⥤ F) (r : C ⥤ E) (rs : D ⥤ F)
    (c : ∀ K : C, eu.obj (r.obj K) ≅ rs.obj (e.obj K))
    (theta : h ⋙ e ≅ (e.op.prod e) ⋙ H)
    (thetaU : hu ⋙ eu ≅ (eu.op.prod eu) ⋙ HU)
    (rho : ∀ K N : D, rs.obj (H.obj (op K, N)) ≅ HU.obj (op (rs.obj K), rs.obj N))
    (restriction : h ⋙ r ≅ (r.op.prod r) ⋙ hu) : Prop :=
  ∀ K N : C,
    eu.map (restriction.hom.app (op K, N)) ≫
      thetaU.hom.app (op (r.obj K), r.obj N) ≫
      HU.map (X := (op (eu.obj (r.obj K)), eu.obj (r.obj N)))
        (Y := (op (rs.obj (e.obj K)), rs.obj (e.obj N)))
        ((c K).inv.op, (c N).hom) =
      (c (h.obj (op K, N))).hom ≫ rs.map (theta.hom.app (op K, N)) ≫
        (rho (e.obj K) (e.obj N)).hom

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (U : X.ProEt)

attribute [local irreducible] sliceRingMonObj

attribute [local irreducible] sliceEquivalence

/-- The same exact equivalence on ordinary unbounded derived categories.
Source: Stacks 05RU (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceDerivedEquivalence :
    DerivedCategory (SliceInternal Λ X U) ≌ DerivedCategory (SliceModules Λ X U) :=
  (sliceEquivalence Λ X U).mapDerivedCategory

/-- The direct derived section functor, in the derived-category universe of the local closed
structure. Upstream's `sliceForward` lands in the standard (larger) universe.
Source: Stacks 05RU (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceDerivedForward :
    DerivedCategory (SliceInternal Λ X U) ⥤ DerivedCategory (SliceModules Λ X U) :=
  (sliceEquivalence Λ X U).functor.mapDerivedCategory

/-- The actual localization comparison for `sliceDerivedForward`.
Source: Stacks 05RU (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceDerivedLocalizationIso :
    DerivedCategory.Q ⋙ sliceDerivedForward Λ X U ≅
      sliceComplexForward Λ X U ⋙ DerivedCategory.Q :=
  (sliceEquivalence Λ X U).functor.mapDerivedCategoryFactors

/-- Derived module restriction, expressed through the section equivalences. Its
underlying sections and maps are the literal slice restriction, by their counits.
Source: Stacks 03DH, 08JB (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceInternalRestriction :
    DerivedCategory (Internal Λ X) ⥤ DerivedCategory (SliceInternal Λ X U) :=
  forward Λ X ⋙
  ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
    (Scheme.ProEt.topology X) (ring Λ X) U ⋙ (sliceDerivedEquivalence Λ X U).inverse

set_option backward.isDefEq.respectTransparency false in
/-- Fix the existing relative module tensor instance for this actual slice ring.
Source: Stacks 03EK; native Mod.monoidalCategory
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
@[instance_reducible, instance] def sliceModuleMonoidal :
    MonoidalCategory (SliceInternal Λ X U) :=
  CategoryTheory.Mod.monoidalCategory

set_option backward.isDefEq.respectTransparency false

attribute [local instance] sliceGradedTensor

attribute [local instance] sliceGradedTensor sliceGradedTensorFour
  sliceGradedTensorLeft sliceGradedTensorRight

set_option backward.isDefEq.respectTransparency false in
/-- Fix the existing native K-flat derived tensor instance once on this slice.
Source: Stacks 06YS; native Mod.derivedMonoidalCategory
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
@[instance_reducible, instance] def sliceDerivedMonoidal :
    MonoidalCategory (DerivedCategory (SliceInternal Λ X U)) :=
  CategoryTheory.Mod.derivedMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
/-- Fix the existing native derived closed structure, without using ringed Hom.
Source: Stacks 08J9; native DerivedCategory.monoidalClosed
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
@[instance_reducible, instance] def sliceDerivedClosed :
    MonoidalClosed (DerivedCategory (SliceInternal Λ X U)) :=
  DerivedCategory.monoidalClosed (SliceInternal Λ X U)

/-- The framework's native local derived internal Hom, independent of the ringed
K-injective model. Source: Stacks 08J9; blueprint derived tensor--Hom
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceNativeHom :
    (DerivedCategory (SliceInternal Λ X U))ᵒᵖ ×
      DerivedCategory (SliceInternal Λ X U) ⥤ DerivedCategory (SliceInternal Λ X U) :=
  Functor.uncurry.obj (MonoidalClosed.internalHom
    (C := DerivedCategory (SliceInternal Λ X U)))

set_option backward.isDefEq.respectTransparency false in
/-- Termwise sections before changing the presentation of the restricted section ring.
Source: Stacks 03DH, 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceRawComplexForward :=
  (sectionModuleFunctor.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
    (sliceRingObject Λ X U)).mapHomologicalComplex (.up ℤ)

/-- The fixed raw total-map type, named before transporting its coefficient presentation.
Source: Stacks 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def SliceRawComplexTensorType (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :=
  (sliceRawComplexForward Λ X U).obj (sliceTotalTensor Λ X U P Q) ≅
    (coefficientTotalTensor.{u, u + 1, u} ((Scheme.ProEt.topology X).over U)
      (sectionRingSheaf.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
        (sliceRingObject Λ X U))).obj
      ((sliceRawComplexForward Λ X U).obj P, (sliceRawComplexForward Λ X U).obj Q)

set_option backward.isDefEq.respectTransparency false in
/-- The actual summand-normalized comparison supplied by the dependency. Every
summand equation in sliceRawComplexTensorComparison determines this map uniquely.
Source: Stacks 03EK, 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceRawComplexTensorIso (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    SliceRawComplexTensorType Λ X U P Q :=
  ordinaryComplexTensorIsoForSite ((Scheme.ProEt.topology X).over U)
    (sliceRingObject Λ X U) P Q

-- Vary only the presentation of the section ring. Explicit functor equalities
-- keep equality transport from unfolding native tensor constructions.
set_option backward.isDefEq.respectTransparency false

private def equivAt (S : Sheaf ((Scheme.ProEt.topology X).over U) CommRingCat.{u + 1})
    (e : sectionRingSheaf.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U) = S) :=
  Eq.mp (congrArg (fun T ↦ SliceInternal Λ X U ≌ SheafOfModules.{u + 1}
    ((sheafCompose ((Scheme.ProEt.topology X).over U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj T)) e)
    (sectionModuleEquivalence.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U))

private def complexAt (S : Sheaf ((Scheme.ProEt.topology X).over U) CommRingCat.{u + 1})
    (e : sectionRingSheaf.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U) = S) :=
  (equivAt Λ X U S e).functor.mapHomologicalComplex (.up ℤ)

private def totalTypeAt
    (P Q : CochainComplex (SliceInternal Λ X U) ℤ)
    (S : Sheaf ((Scheme.ProEt.topology X).over U) CommRingCat.{u + 1})
    (e : sectionRingSheaf.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U) = S) : Type (u + 1) :=
  (complexAt Λ X U S e).obj (sliceTotalTensor Λ X U P Q) ≅
    (coefficientTotalTensor.{u, u + 1, u} ((Scheme.ProEt.topology X).over U) S).obj
      ((complexAt Λ X U S e).obj P, (complexAt Λ X U S e).obj Q)

private theorem family_type_eq {A : Type u₀} (a : A)
    (T : ∀ b : A, a = b → Type (u + 1)) (b : A) (h : a = b) :
    T b h = T a rfl := by
  cases h
  rfl

attribute [local irreducible] sliceComplexForward sliceRawComplexTensorIso

private theorem complexAt_eq :
    complexAt Λ X U _ (sliceSectionRing_eq Λ X U) = sliceComplexForward Λ X U := by
  unfold complexAt equivAt sliceComplexForward sliceEquivalence
  rfl

private theorem totalTypeAt_eq (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    totalTypeAt Λ X U P Q _ (sliceSectionRing_eq Λ X U) =
      ((sliceComplexForward Λ X U).obj (sliceTotalTensor Λ X U P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} ((Scheme.ProEt.topology X).over U)
        ((ring Λ X).over U)).obj
        ((sliceComplexForward Λ X U).obj P, (sliceComplexForward Λ X U).obj Q)) := by
  unfold totalTypeAt
  rw [complexAt_eq]

/-- The literal and reconstructed section-ring presentations give equal total-map types.
Source: Stacks 03DH, 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison).
Proof: the generic dependent family of total-map types transports along
sliceSectionRing_eq; equality elimination identifies it with the raw type. -/
theorem sliceTotalComparison_type_eq (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    ((sliceComplexForward Λ X U).obj (sliceTotalTensor Λ X U P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} ((Scheme.ProEt.topology X).over U)
        ((ring Λ X).over U)).obj
        ((sliceComplexForward Λ X U).obj P, (sliceComplexForward Λ X U).obj Q)) =
      SliceRawComplexTensorType Λ X U P Q := by
  rw [← totalTypeAt_eq]
  exact family_type_eq _ (totalTypeAt Λ X U P Q) _ (sliceSectionRing_eq Λ X U)

/-- The uniquely summand-normalized local total comparison.
Source: Stacks 03EK, 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
@[irreducible]
def sliceTotalComparison (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    (sliceComplexForward Λ X U).obj (sliceTotalTensor Λ X U P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} ((Scheme.ProEt.topology X).over U)
        ((ring Λ X).over U)).obj
        ((sliceComplexForward Λ X U).obj P, (sliceComplexForward Λ X U).obj Q) :=
  cast (sliceTotalComparison_type_eq Λ X U P Q).symm
    (sliceRawComplexTensorIso Λ X U P Q)

set_option backward.isDefEq.respectTransparency true

/-- An isomorphism with a fixed normalization condition, independent of its endpoints.
Source: Stacks 06YS (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
structure NormalizedSliceTensorComparisonData {I : Type u₀} (condition : I → Prop) where
  iso : I
  normalization : condition iso

/-- Closed structures for the fixed local ringed-site Hom, with named endpoints.
Source: Stacks 08J9 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def SliceClosedStructureType := CoefficientClosedStructure
  (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
    ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))

/-- Tensor models for that fixed local closed structure.
Source: Stacks 06YS (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def SliceTensorModelsType (SU : SliceClosedStructureType Λ X U) :=
  CoefficientTensorModels.{u, u + 1, u, u + 1}
    ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU

/-- Natural comparisons of the fixed native slice tensor.
Source: Stacks 06YS (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def SliceTensorComparisonIsoType (SU : SliceClosedStructureType Λ X U) :=
  sliceNativeTensor Λ X U ⋙ (sliceDerivedForward Λ X U) ≅
    ((sliceDerivedForward Λ X U).prod (sliceDerivedForward Λ X U)) ⋙ SU.tensor

/-- Representative normalization of the local derived tensor comparison, for every
pair with K-flat section images. No derived input is required to be flat.
Source: Stacks 06YS, 08J9 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceTensorComparisonNormalized
    (SU : SliceClosedStructureType Λ X U)
    (TU : SliceTensorModelsType Λ X U SU)
    (iso : SliceTensorComparisonIsoType Λ X U SU) : Prop :=
  tensorLocalizationSquareHEq DerivedCategory.Q DerivedCategory.Q
    (sliceComplexForward Λ X U) (sliceDerivedForward Λ X U) (sliceDerivedLocalizationIso Λ X U)
    (sliceNativeTensor Λ X U)
    (MonoidalCategory.tensor (CochainComplex (SliceInternal Λ X U) ℤ)) SU.tensor
    (coefficientTotalTensor.{u, u + 1, u} ((Scheme.ProEt.topology X).over U)
      ((ring Λ X).over U))
    (sliceLocalizationTensorMap Λ X U) (sliceTotalComparison Λ X U)
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := (Scheme.ProEt.topology X).over U) (R := (ring Λ X).over U))
    (CoefficientTensorModels.iso.{u, u + 1, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU TU) iso

/-- Comparison of native local derived tensors, fixed by their K-flat models.
Source: Stacks 06YS, 08J9 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
abbrev SliceTensorComparison
    (SU : SliceClosedStructureType Λ X U)
    (TU : SliceTensorModelsType Λ X U SU) :=
  NormalizedSliceTensorComparisonData (I := SliceTensorComparisonIsoType Λ X U SU)
    (sliceTensorComparisonNormalized Λ X U SU TU)

private theorem nativeMonoidal_eq_localization
    (C : Type u₀) [Category.{v₀} C] [Abelian C] [IsGrothendieckAbelian.{v₀} C]
    [HasDerivedCategory.{v₀} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C]
    [(DerivedCategory.Qh (C := C)).HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (.up ℤ))] :
    DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory C =
      DerivedMonoidal.instMonoidalCategory DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (.up ℤ)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The framework's local monoidal structure is its K-flat localization structure.
Source: Stacks 06YS (blueprint: def-sfb-internal-slice-derived-hom-comparison).
Proof: unfold Mod.derivedMonoidalCategory; both instances use the same native
K-flat derivability structure and total tensor, hence identical monoidal data. -/
theorem sliceMonoidal_eq_localization :
    (inferInstance : MonoidalCategory (DerivedCategory (SliceInternal Λ X U))) =
      DerivedMonoidal.instMonoidalCategory DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SliceInternal Λ X U) (.up ℤ)) := by
  exact nativeMonoidal_eq_localization (SliceInternal Λ X U)

set_option backward.isDefEq.respectTransparency false in
/-- The actual localized Koszul braiding on the native local derived tensor.
Source: Stacks 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
instance sliceBraiding : BraidedCategory (DerivedCategory (SliceInternal Λ X U)) :=
  Eq.mp (congrArg (fun m ↦ @BraidedCategory (DerivedCategory (SliceInternal Λ X U)) _ m)
    (sliceMonoidal_eq_localization Λ X U).symm)
    (DerivedMonoidal.braidedCategory' DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SliceInternal Λ X U) (.up ℤ)))

/-- The native closed-structure counit, written with Hom as the first tensor factor.
Source: Stacks 08J9 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceNativeEvaluation (K N : DerivedCategory (SliceInternal Λ X U)) :
    (sliceNativeTensor Λ X U).obj ((sliceNativeHom Λ X U).obj (op K, N), K) ⟶ N :=
  (@BraidedCategory.braiding _ _ _ (sliceBraiding Λ X U)
    ((sliceNativeHom Λ X U).obj (op K, N)) K).hom ≫
      (MonoidalClosed.internalHomAdjunction₂.adj K).counit.app N

/-- The local section functor commutes with restriction through its fixed counit.
Source: Stacks 03DH, 08JB (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceRestrictionSectionIso (K : DerivedCategory (Internal Λ X)) :
    (sliceDerivedForward Λ X U).obj ((sliceInternalRestriction Λ X U).obj K) ≅
      (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) U).obj ((forward Λ X).obj K) :=
  (sliceDerivedEquivalence Λ X U).counitIso.app _

set_option maxHeartbeats 600000 in
-- The dependent counit and restriction equations have large derived-category endpoint types.
/-- The local comparison identifies the native local tensor-Hom counit.
Source: Stacks 08J9, Step 5 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceHomEvaluationNormalized
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU)
    (tU : SliceTensorComparison Λ X U SU TU)
    (iso : sliceNativeHom Λ X U ⋙ (sliceDerivedForward Λ X U) ≅
    (((sliceDerivedForward Λ X U).op).prod
      (sliceDerivedForward Λ X U)) ⋙
      derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)) : Prop :=
  homEvaluationSquare (sliceNativeTensor Λ X U) (sliceNativeHom Λ X U)
    (sliceNativeEvaluation Λ X U) (sliceDerivedForward Λ X U) SU.tensor
    (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
    SU.evaluation tU.iso iso

set_option maxHeartbeats 600000 in
-- The dependent counit and restriction equations have large derived-category endpoint types.
/-- The module-side restriction is the unique lift of the normalized ringed Hom
square through the local section equivalence, with its canonical counits.
Source: Stacks 08JB, Step 5 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceHomRestrictionCompatible
    (S : CoefficientClosedStructure (hom Λ X))
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (d : RingedSliceEvaluationComparisons (hom Λ X)
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
      (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) U) S SU
      (RingedSliceFlatRestriction.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring Λ X) U))
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X)
    (iso : sliceNativeHom Λ X U ⋙ (sliceDerivedForward Λ X U) ≅
    (((sliceDerivedForward Λ X U).op).prod
      (sliceDerivedForward Λ X U)) ⋙
      derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
    (restriction : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙
      sliceInternalRestriction Λ X U ≅
    ((sliceInternalRestriction Λ X U).op.prod (sliceInternalRestriction Λ X U)) ⋙
      sliceNativeHom Λ X U) : Prop :=
  homRestrictionSquare (Functor.uncurry.obj (CondensedRing.derivedHom Λ X))
    (sliceNativeHom Λ X U) (hom Λ X)
    (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
    (forward Λ X) (sliceDerivedForward Λ X U) (sliceInternalRestriction Λ X U)
    (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
      (Scheme.ProEt.topology X) (ring Λ X) U)
    (sliceRestrictionSectionIso Λ X U) θ iso d.eta restriction

/-- Evaluation-normalized comparison for every local module object, and its
compatibility with restriction of the global comparison. The two named predicates
retain the local counit equation and the full module-object restriction square.
Source: Stacks 08J9, 08JB (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
structure SliceHomComparison
    (S : CoefficientClosedStructure (hom Λ X))
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU)
    (tU : SliceTensorComparison Λ X U SU TU)
    (d : RingedSliceEvaluationComparisons (hom Λ X)
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
      (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) U) S SU
      (RingedSliceFlatRestriction.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring Λ X) U))
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X) where
  /-- The comparison on all B|U-module objects, in both derived variables. -/
  iso : sliceNativeHom Λ X U ⋙ (sliceDerivedForward Λ X U) ≅
    (((sliceDerivedForward Λ X U).op).prod
      (sliceDerivedForward Λ X U)) ⋙
      derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)
  /-- The local isomorphism identifies the two actual adjunction counits. -/
  evaluation : sliceHomEvaluationNormalized Λ X U SU TU tU iso
  /-- Restriction of the actual global module-object Hom to the actual local Hom. -/
  restriction : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙
      sliceInternalRestriction Λ X U ≅
    ((sliceInternalRestriction Λ X U).op.prod (sliceInternalRestriction Λ X U)) ⋙
      sliceNativeHom Λ X U
  /-- The module-side restriction and both Hom comparisons form the source square. -/
  compatibility : sliceHomRestrictionCompatible Λ X U S SU d θ iso restriction

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
