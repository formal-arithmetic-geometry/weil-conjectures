/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NY and Q86
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.AlgebraicGeometry.SupportCohomology
import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison
import Sheaf.AlgebraicGeometry.SupportQuotientFlat
import Sheaf.AlgebraicGeometry.SupportQuotientProduct
import Sheaf.AlgebraicGeometry.SupportedProductQuotientModel
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Comparison of ordinary supported sections between the two sites

Source: Stacks Project, Tags 099W, 099V, 09B1 and 09XP, with the supported
refinement of blueprint `lem-pur-support-site-comparison`
(blueprint: lem-pur-support-site-comparison).

## Main definitions and statements

* `ProEtale.supportComparison`: the natural bounded-below comparison map.
* `ProEtale.supportComparison_isIso`: invertibility under the node's hypotheses.
* `ProEtale.supportComparison_forget`, `ProEtale.fullSupportForget_isIso`, and
  `ProEtale.supportComparison_open`: forgetting, full-support normalization, and restriction.
* `ProEtale.supportExteriorCoefficientIso`: the specified tensor/pullback comparison theta.
* `ProEtale.supportComparison_exterior`: equality of the supported exterior-product maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ v₃ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A]
  {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]

/-- The etale support kernel used by the canonical comparison unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev etaleSupportKernel :=
  Sheaf.supportedSectionsFunctor T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (Etale.supportRestrictionArrow i)

/-- The support comparison unit is uniquely normalized by the adjunction-unit
map on sections and the kernel inclusion.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: sections identify with evaluation at the final object.  The comparison
adjunction unit commutes with restriction, so it maps the etale support kernel
into the pro-etale kernel.  The kernel universal property gives the map and its
inclusion equation gives uniqueness. -/
theorem supportComparisonUnit_existsUnique :
    ∃! c : etaleSupportKernel A i ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ supportSections i A,
      ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
        c.app F ≫ kernel.ι
          (((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F).obj.map
            (supportRestrictionArrow i).op) =
        (Sheaf.supportedSectionsInclusion T.smallEtaleTopology
          (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i)).app F ≫
          (((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 T)))) := by
  sorry

/-- The canonical ordinary support comparison unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportComparisonUnit :=
  Classical.choose (supportComparisonUnit_existsUnique A i)

/-- The canonical bounded-below derived support comparison induced by the unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: apply the right-derived-functor-plus base-change construction to the
unit-normalized ordinary support map, inserting the canonical identity
unitors and the derived-category-plus identity comparison. -/
noncomputable def supportComparison :
    (etaleSupportKernel A i).rightDerivedFunctorPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        (supportSections i A).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := etaleSupportKernel A i) (G' := supportSections i A)
      (β := comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ supportComparisonUnit A i)

/-- Under finite algebraically closed field hypotheses this canonical support map
is an isomorphism.
Source: Stacks Tags 099V(2), 099W(2), 09B1(2), 09XP and blueprint
proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: direct image restricts to the etale subsite, so the support kernels are
termwise the same on injective resolutions.  Exact comparison inverse image makes
its right adjoint preserve injectives, and the bounded-below comparison unit is
invertible.  The derived support map is therefore invertible. -/
theorem supportComparison_isIso (k : Type u) [Field k] [IsAlgClosed k]
    [T.Over (Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [Finite A] : IsIso (supportComparison A i) := by
  sorry

/-- The canonical identification of the global-section kernel with the restriction
kernel used by the support long exact sequence.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: the terminal-evaluation isomorphism identifies global restriction with
restriction from the terminal object. It induces an isomorphism of kernels.
The kernel inclusion determines its forward map and hence the isomorphism uniquely. -/
theorem supportKernelEvaluationIso_existsUnique :
    ∃! e : Etale.supportedEtaleSections A T i.openComplement ≅ etaleSupportKernel A i,
      e.hom ≫ Sheaf.supportedSectionsInclusion T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) =
      Etale.supportedEtaleSectionsι A T i.openComplement ≫
        (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).hom := by
  sorry

/-- The uniquely kernel-normalized terminal-evaluation transport.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportKernelEvaluationIso :=
  Classical.choose (supportKernelEvaluationIso_existsUnique A i)

/-- The existing global-section presentation of the etale support functor.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev globalEtaleSupportKernel :=
  Etale.supportedEtaleSections A T i.openComplement

/-- The bounded-below comparison viewed in unbounded `D(A)`, using the canonical
compatibility of the two right-derived-functor constructions.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportComparisonUnbounded
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (globalEtaleSupportKernel A i).rightDerivedFunctor.obj M.obj ⟶
      (supportSections i A).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) :=
  (Functor.rightDerivedFunctorNatTrans (supportKernelEvaluationIso A i).hom).app M.obj ≫
    (etaleSupportKernel A i).rightDerivedFunctorPlusCompatibility.inv.app M ≫
    DerivedCategory.Plus.ι.map ((supportComparison A i).app M) ≫
    (supportSections i A).rightDerivedFunctorPlusCompatibility.hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj M)

/-- The published inclusion of the ordinary etale support kernel into global sections.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev etaleSupportForget := Etale.supportedEtaleSectionsι A T i.openComplement

/-- Reuse the published inclusion of pro-etale supported sections.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev proEtaleSupportForget := supportedModuleSectionsι A i

/-- Terminal evaluation for etale modules, with its explicit additive functor type.
Source: blueprint full-support normalization (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportEtaleGlobalEvaluationIso (T : Scheme.{u}) :
    Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ≅
      sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T))) :=
  Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)

/-- Terminal evaluation for pro-etale modules in the same additive presentation.
Source: blueprint full-support normalization (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportProEtaleGlobalEvaluationIso (T : Scheme.{u}) :
    Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ≅
      sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T))) :=
  Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
    (Scheme.ProEt.isTerminalMkId T)

/-- The specified finite global comparison, in the global-sections presentation.
The only inserted maps are terminal evaluation and D+/unbounded derived compatibility.
Source: blueprint full-support normalization (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportGlobalComparison [Finite A]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctor.obj M.obj ⟶
      (Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) :=
  (Functor.rightDerivedFunctorNatTrans
    (supportEtaleGlobalEvaluationIso A T).hom).app M.obj ≫
  (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))).rightDerivedFunctorPlusCompatibility.inv.app
      M ≫
  DerivedCategory.Plus.ι.map
    (((Functor.rightUnitor _).inv ≫
      (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
        (ModuleCat.{u + 1} A))).inv ≫ finiteComparisonGlobalSections T A).app M) ≫
  (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj
      (op (Scheme.ProEt.mk (𝟙 T)))).rightDerivedFunctorPlusCompatibility.hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj M) ≫
  (Functor.rightDerivedFunctorNatTrans
    (supportProEtaleGlobalEvaluationIso A T).inv).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj)

/-- The square for forgetting support commutes with the existing adjunction-unit
comparison of global sections.
Source: Stacks Tags 099W and 09XP; blueprint proof paragraph 1
(blueprint: lem-pur-support-site-comparison).
Proof: compose the ordinary comparison kernel map with its kernel inclusion.
Kernel functoriality gives evaluation of the ordinary comparison unit at `T`.
Apply the right-derived universal property to this commuting square; on
K-injective direct images it is literally the same square in each degree.
The terminal-evaluation transport in `supportGlobalComparison` has this normalization. -/
theorem supportComparison_forget [Finite A]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    supportComparisonUnbounded A i M ≫
      (Functor.rightDerivedFunctorNatTrans (proEtaleSupportForget A i)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
    (Functor.rightDerivedFunctorNatTrans (etaleSupportForget A i)).app M.obj ≫
      supportGlobalComparison A (T := T) M := by
  sorry

/-- With full support, the forgetful maps are isomorphisms. Together with the
preceding square this states that the full-support comparison is exactly the
existing global-sections comparison induced by the adjunction unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: the complement of the identity immersion is empty. A module sheaf has zero
sections over the empty scheme, so each restriction kernel is its source and its
kernel inclusion is invertible. Derive these natural isomorphisms. The preceding
square identifies the full-support comparison with the specified global one. -/
theorem fullSupportForget_isIso (T : Scheme.{u}) :
    IsIso (Functor.rightDerivedFunctorNatTrans (etaleSupportForget A (𝟙 T))) ∧
      IsIso (Functor.rightDerivedFunctorNatTrans (proEtaleSupportForget A (𝟙 T))) := by
  sorry

/-- Derive the recorded coefficient pullback comparison before specializing coefficients.
Source: blueprint comparison-pullback clause (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportDerivedCoefficientPullbackIso
    (D : Type v₁) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar D f).mapDerivedCategory ⋙
        (comparisonUpperStar D X).mapDerivedCategory ≅
      (comparisonUpperStar D Y).mapDerivedCategory ⋙ (upperStar D f).mapDerivedCategory :=
  let e : Etale.upperStar D f ⋙ comparisonUpperStar D X ≅
      comparisonUpperStar D Y ⋙ upperStar D f :=
    supportSiteComparisonCoefficientPullbackIso D f
  (Functor.mapDerivedCategoryCompIso (Etale.upperStar D f)
    (comparisonUpperStar D X)).symm ≪≫
  Functor.mapDerivedCategoryNatIso e ≪≫
  Functor.mapDerivedCategoryCompIso (comparisonUpperStar D Y) (upperStar D f)

/-- Exact coefficient pullback comparison on unbounded derived categories, formed
from the recorded, unit-normalized comparison-pullback isomorphism.
Source: blueprint comparison-pullback clause (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportDerivedPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory :=
  supportDerivedCoefficientPullbackIso (ModuleCat.{u + 1} A) f

open MonoidalCategory

/-- Apply the existing bifunctor to two isomorphisms without unfolding a
scheme-indexed monoidal instance.
Source: blueprint tensor comparison (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportBifunctorIso
    {C : Type v₁} {D : Type v₂} {E : Type v₃}
    [Category.{w₁} C] [Category.{w₂} D] [Category.{w₃} E]
    (B : C ⥤ D ⥤ E) {M M' : C} {N N' : D} (a : M ≅ M') (b : N ≅ N') :
    (B.obj M).obj N ≅ (B.obj M').obj N' :=
  (B.mapIso a).app N ≪≫ (B.obj M').mapIso b

/-- The canonical derived monoidal comparison, assembled from the general
left-derived tensor comparison and exact/left-derived identifications. Generic
coefficients keep their categorical structures abstract during elaboration.
Source: blueprint specified theta (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportDerivedComparisonTensorIso
    (D : Type v₁) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) [(comparisonUpperStar D T).PreservesFlat]
    (K L : DerivedCategory (Sheaf T.smallEtaleTopology D)) :
    (comparisonUpperStar D T).mapDerivedCategory.obj (((Etale.derivedTensor D T).obj K).obj L) ≅
      ((derivedTensor D T).obj ((comparisonUpperStar D T).mapDerivedCategory.obj K)).obj
        ((comparisonUpperStar D T).mapDerivedCategory.obj L) :=
  (comparisonUpperStar D T).leftDerivedFunctorIsoMapDerivedCategory.symm.app
      (((Etale.derivedTensor D T).obj K).obj L) ≪≫
    ((asIso (comparisonUpperStar D T).leftDerivedTensorComparison).app K).app L ≪≫
    supportBifunctorIso (derivedTensor D T)
      ((comparisonUpperStar D T).leftDerivedFunctorIsoMapDerivedCategory.app K)
      ((comparisonUpperStar D T).leftDerivedFunctorIsoMapDerivedCategory.app L)

/-- The specified exterior-product coefficient comparison: tensor comparison followed
by the two canonical comparison-pullback identifications.
Source: blueprint displayed `theta` (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportExteriorCoefficientIso [Finite A]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory.obj
      (Etale.externalProduct (ModuleCat.{u + 1} A) f g K L) ≅
    externalProduct (ModuleCat.{u + 1} A) f g
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory.mapIso
    (supportBifunctorIso (Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst f g)).app K)
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd f g)).app L)) ≪≫
  supportDerivedComparisonTensorIso (ModuleCat.{u + 1} A) (pullback f g)
    ((Etale.upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).mapDerivedCategory.obj K)
    ((Etale.upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).mapDerivedCategory.obj L) ≪≫
  supportBifunctorIso (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    ((supportDerivedPullbackIso A (pullback.fst f g)).app K)
    ((supportDerivedPullbackIso A (pullback.snd f g)).app L) ≪≫
  supportBifunctorIso (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.fst f g)).symm.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.snd f g)).symm.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L)) ≪≫
  eqToIso (supportedExternalProduct_eq A f g
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L))

/-- Compatibility with both supported exterior products in the unbounded derived
category of ordinary modules; the boundedness hypothesis is imposed on the actual
exterior product, rather than implicitly assuming it follows from its inputs.
Source: Stacks Tags 0H9A and 07A4; blueprint proof paragraphs 2--8
(blueprint: lem-pur-support-site-comparison).
Proof: form the quotient of the free constant sheaf by the free sheaf of the
open complement. It represents supported sections by the kernel/cokernel Yoneda
bijection. Its geometric etale stalks are zero or A, hence it is flat; comparison
pullback gives the pro-etale quotient and its flatness without using pro-etale
stalk conservativity. Quotient multiplication identifies the tensor of the two
pulled-back quotients with the product-support quotient. All maps preserve quotient
generators. The exact constant-with-support functors are left adjoint to the actual
unbounded derived support functors. Comparison of supports is the transpose of
the pulled-back counit, since both transposes send a section to its adjunction-unit
image. The exterior product is the transpose of the tensor of the two pulled-back
counits through the generator-normalized product identification. Pullback and tensor
coherence identify that identification in both topologies. Transpose both sides of
the displayed equation under the product-support adjunction. The two comparison
counit identities and monoidal coherence make the transposes equal. Injectivity of
the Hom bijection proves the equation. K-flat localization identifies these maps
with the pairing derived using K-flat tensor and injective support resolutions. -/
theorem supportComparison_exterior [Finite A] (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (F : DerivedCategory.Plus
      (Sheaf (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))).smallEtaleTopology
        (ModuleCat.{u + 1} A)))
    (eF : F.obj ≅ Etale.externalProduct (ModuleCat.{u + 1} A)
      (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) K.obj L.obj) :
    Etale.supportedExteriorProduct A (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j K.obj L.obj ≫
      (globalEtaleSupportKernel A
        (Etale.supportedProductImmersion
          (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j)).rightDerivedFunctor.map
          eF.inv ≫
      supportComparisonUnbounded A
        (Etale.supportedProductImmersion (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j) F ≫
      (supportSections
        (Etale.supportedProductImmersion
          (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j) A).rightDerivedFunctor.map
        ((comparisonUpperStar (ModuleCat.{u + 1} A)
          (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)))).mapDerivedCategory.map eF.hom ≫
          (supportExteriorCoefficientIso A (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))
            K.obj L.obj).hom) =
    tensorHom (supportComparisonUnbounded A i K) (supportComparisonUnbounded A j L) ≫
      supportedExteriorProductOverField A k (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry


namespace ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A] {C T U : Scheme.{u}}
  [IsLocallyNoetherian T] [IsLocallyNoetherian U]
  (i : C ⟶ T) [IsClosedImmersion i] (v : U ⟶ T) [IsOpenImmersion v]

/-- Pullback of the support quotient, determined by its constant quotient map.
Source: blueprint proof paragraphs 1 and 3 (blueprint: lem-pur-support-site-comparison).
Proof: inverse image takes the free sheaf on an open to the free sheaf on its
inverse image. It preserves the cokernel defining supported constants, and the
inverse image of the complement is the complement of the pulled-back support.
This produces the normalized isomorphism. Its quotient map is epimorphic, so the
normalization determines it at every coefficient module, hence uniquely as a
natural isomorphism. In the pro-etale topology this is also the pullback of the
etale quotient construction through comparison. -/
theorem supportOpenConstantIso_existsUnique :
    ∃! e : supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) v ≅
      supportedCoefficients A (pullback.snd i v),
      ∀ M : ModuleCat.{u + 1} A,
        (upperStar (ModuleCat.{u + 1} A) v).map (supportedCoefficientQuotient A i M) ≫
          e.hom.app M =
        (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) v).hom.app M ≫
          supportedCoefficientQuotient A (pullback.snd i v) M := by
  sorry

/-- The normalized open pullback of the supported constant functor.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenConstantIso :
    supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) v ≅
      supportedCoefficients A (pullback.snd i v) :=
  Classical.choose (supportOpenConstantIso_existsUnique A i v)

/-- The exact derived open pullback of the quotient functor.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenDerivedConstantIso :
    (supportedCoefficients A i).mapDerivedCategory ⋙
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ≅
        (supportedCoefficients A (pullback.snd i v)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (supportedCoefficients A i)
    (upperStar (ModuleCat.{u + 1} A) v)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (supportOpenConstantIso A i v)

/-- Restriction of derived supported sections to an open: transpose the pulled-back
support counit using the uniquely quotient-normalized base-change identification.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenRestriction
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  (supportedCoefficientDerivedAdjunction A (pullback.snd i v)).homEquiv _ _
    ((supportOpenDerivedConstantIso A i v).inv.app
      ((supportSections i A).rightDerivedFunctor.obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
        ((supportedCoefficientDerivedAdjunction A i).counit.app K))

end ProEtale

namespace ProEtale

/-- Open restriction with local Noetherianity supplied by finite type over the field.
Source: blueprint open-restriction clause (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenRestrictionOverField
    (A : Type (u + 1)) [CommRing A] [Finite A] (k : Type u) [Field k]
    {C T U : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    (i : C ⟶ T) [IsClosedImmersion i] (v : U ⟶ T) [IsOpenImmersion v]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  letI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian v
  supportOpenRestriction A i v K

/-- The comparison commutes with canonical restriction to every open, with the
specified comparison-pullback coefficient transport on the restricted object.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: restriction commutes with the support kernel because both maps restrict
the same sections. Open restriction preserves K-injectives: its extension-by-zero
left adjoint is exact in each topology. Thus on restricted K-injective direct
images the same kernel square computes the derived restriction square. The
comparison unit commutes with this square by adjunction, since both restricted
units are transposes of the identity. The pro-etale quotient-normalized transpose
is this same restriction map by the support adjunction. The etale arrow reuses
`Etale.derivedSupportOpenRestriction`,
normalized by ordinary kernel restriction and the derived-composition unit.
Therefore the two paths are equal, with exactly the canonical pullback coefficient
identification displayed on the last map. -/
theorem supportComparison_open (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {C T : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (i : C ⟶ T) [IsClosedImmersion i] (U : T.Opens)
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    supportComparisonUnbounded A i M ≫
      supportOpenRestrictionOverField A k i U.ι
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
    (Etale.derivedSupportOpenRestriction A i U).app M.obj ≫
      supportComparisonUnbounded A (pullback.snd i U.ι)
        ((Etale.upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategoryPlus.obj M) ≫
      (supportSections (pullback.snd i U.ι) A).rightDerivedFunctor.map
        ((supportDerivedPullbackIso A U.ι).hom.app M.obj) := by
  sorry

end ProEtale
end AlgebraicGeometry
