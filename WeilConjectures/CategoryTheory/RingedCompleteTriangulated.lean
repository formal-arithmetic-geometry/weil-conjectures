/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
public import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlatSupplement
public import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
public import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
public import WeilConjectures.Algebra.Homology.InternalHom
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
public import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
public import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation
public import WeilConjectures.CategoryTheory.RingedKoszulDualizable
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
public import WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic
public import WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
public import WeilConjectures.Algebra.Homology.ExactProductsRoosComparisonSupplement
public import WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower
public import WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
public import WeilConjectures.Algebra.Homology.TelescopeColimit
public import WeilConjectures.Algebra.Homology.SignedDoubleHomConeSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModelSupplement
public import WeilConjectures.CategoryTheory.RingedAugmentedCechRestriction
public import WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
public import WeilConjectures.AlgebraicGeometry.RingedLocalizationRestrictionSupplement
public import WeilConjectures.Algebra.Homology.SliceTensorNatural
public import WeilConjectures.Algebra.Homology.SliceModuleSheafification
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestrictionSupplement
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # Exact Koszul completion and the triangulated complete locus

Source: Stacks Project, algebraization.tex, Tags 0A0E and 099B, and the paragraph after
Definition 0999 (blueprint: lem-sfb-ringed-complete-triangulated).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The reflector onto a strictly full triangulated subcategory is exact, with
shift structure compatible with its specified unit. This is the left-adjoint form of
Mathlib's triangulated-adjoint theorem, applied to the full-subcategory inclusion. -/
private theorem exact_reflector
    {A : Type*} [Category* A] [HasZeroObject A] [Preadditive A] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (F : A ⥤ A) (η : 𝟭 A ⟶ F) (hc : ∀ X, P (F.obj X))
    (hb : ∀ X Y, P Y → Function.Bijective (fun a : F.obj X ⟶ Y ↦ η.app X ≫ a)) :
    ∃ _s : F.CommShift ℤ, F.IsTriangulated ∧ NatTrans.CommShift η ℤ := by
  classical
  let L := P.lift F hc
  let e (X : A) (Y : P.FullSubcategory) :
      (L.obj X ⟶ Y) ≃ (X ⟶ P.ι.obj Y) :=
    P.fullyFaithfulι.homEquiv.trans
      (Equiv.ofBijective (fun a ↦ η.app X ≫ a) (hb X Y.obj Y.property))
  let adj : L ⊣ P.ι := Adjunction.mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply (e X' Y).injective
        change η.app X' ≫ ((e X' Y).symm (f ≫ g)).hom =
          η.app X' ≫ F.map f ≫ ((e X Y).symm g).hom
        rw [← Category.assoc, ← η.naturality f, Category.assoc]
        exact (e X' Y).apply_symm_apply (f ≫ g) |>.trans
          (congrArg (fun a ↦ f ≫ a) ((e X Y).apply_symm_apply g)).symm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        change η.app X ≫ (f.hom ≫ g.hom) = (η.app X ≫ f.hom) ≫ g.hom
        exact (Category.assoc _ _ _).symm }
  have hunit : adj.unit = η := by
    ext X
    change η.app X ≫ 𝟙 _ = η.app X
    exact Category.comp_id _
  let sL := adj.leftAdjointCommShift ℤ
  have hAdj : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have hL : L.IsTriangulated := adj.isTriangulated_leftAdjoint
  let sF : F.CommShift ℤ :=
    Functor.CommShift.ofIso (P.liftCompιIso F hc) ℤ
  have he : NatTrans.CommShift (P.liftCompιIso F hc).hom ℤ :=
    Functor.CommShift.ofIso_compatibility (P.liftCompιIso F hc) ℤ
  have hF : F.IsTriangulated := Functor.isTriangulated_of_iso (P.liftCompιIso F hc)
  have hη : NatTrans.CommShift η ℤ := by
    have h : η = adj.unit ≫ (P.liftCompιIso F hc).hom := by
      rw [hunit]
      ext X
      exact (Category.comp_id _).symm
    rw [h]
    exact NatTrans.CommShift.comp adj.unit (P.liftCompιIso F hc).hom ℤ
  exact ⟨sF, hF, hη⟩

/-- Koszul completion is exact, its prescribed unit commutes with all integer shifts,
and the local derived-complete locus is a strictly full triangulated subcategory.

Source: Stacks Project, algebraization.tex, Tags 0A0E and 099B, and the paragraph after
Definition 0999 (blueprint: lem-sfb-ringed-complete-triangulated).

The mono `ι` and `hgen` represent exactly the ideal generated by the finite list `b`.
The list may be empty. `RingedKoszulLimitPresentation` fixes the strict Koszul tower,
its descent and total derived inverse limit, and `D.unit` is its degree-zero unit.
Its index `m : ℕ` denotes exponent `m+1`. The presentation uses the dual of the positive
Koszul complex, the negative Koszul complex of Tag 0A0E. No boundedness, Noetherian
condition or exactness of products is imposed. The existential shift structure is
induced by the reflector adjunction and is compatible with the prescribed unit.
The natural transformation is required to have precisely the prescribed components;
its `CommShift` property supplies the natural morphism of distinguished image triangles
via `NatTrans.mapTriangle`, including compatibility with maps of triangles.

Proof:
1. On each slice and for each section of the ideal, compose exact derived restriction
   with derived internal Hom from its localization. The existing theorem
   `ringedInternalHom_exact` supplies integer shifts and exactness of this Hom functor
   (Stacks, sites-cohomology.tex, Tag 08JC).
2. Local completeness is simultaneous vanishing of these exact functors. Mapping an
   isomorphism preserves vanishing; exact functors send zero to zero; their shift
   comparisons preserve vanishing under all integer shifts. In a distinguished triangle,
   zero first and third images force zero middle image. Thus the local predicate itself
   defines a strictly full triangulated subcategory (Tag 0999 and its following paragraph).
3. Obtain the actual strict Koszul presentation, output completeness, naturality and
   mapping bijection from `ringedKoszulCompletionReflector` (Tags 099B and 0A0E).
   Lift its completion functor to the complete full subcategory. Precomposition with
   precisely `D.unit` defines the Hom equivalence for an adjunction to its inclusion.
   The identity map gives the adjunction unit, which equals the prescribed unit.
4. The inclusion is triangulated. Its left adjoint acquires a coherent shift structure
   from the adjunction and is triangulated by Mathlib's triangulated-adjoint theorem.
   Composing with inclusion and transporting through the canonical lift comparison gives
   exact completion. The adjunction unit commutes with shifts; the proved equality with
   the prescribed unit supplies the required natural transformation and its `CommShift`.
   This argument is the private helper `exact_reflector`, proved above. -/
theorem ringedCompleteTriangulated
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι]
    (hgen : ∀ U : C, IsRingedIdealGeneratingList O I ι U r
      (fun i ↦ (b i).val (op U))) :
    ∃ (D : RingedKoszulLimitPresentation O r b) (_hshift : D.completion.CommShift ℤ),
      D.completion.IsTriangulated ∧
      (∃ η : 𝟭 (ringedSiteDerived O) ⟶ D.completion,
        (∀ N : ringedSiteDerived O, η.app N = D.unit N) ∧ NatTrans.CommShift η ℤ) ∧
      ObjectProperty.IsClosedUnderIsomorphisms (IsLocallyDerivedRingedIdealComplete O I ι) ∧
      ObjectProperty.IsTriangulated (IsLocallyDerivedRingedIdealComplete O I ι) := by
  classical
  let : Zero (ringedSiteDerived O) := HasZeroObject.zero' _
  let P : ObjectProperty (ringedSiteDerived O) := IsLocallyDerivedRingedIdealComplete O I ι
  let hRshift (U : C) : (ringedDerivedRestriction O U).CommShift ℤ := by
    unfold ringedDerivedRestriction
    infer_instance
  let hRtri (U : C) : (ringedDerivedRestriction O U).IsTriangulated := by
    unfold ringedDerivedRestriction
    infer_instance
  let H (U : C) (f : O.obj.obj (op U)) :=
    (Functor.curry.obj (derivedInternalHom (J.over U) (O.over U))).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))))
  have hPiso : P.IsClosedUnderIsomorphisms := by
    constructor
    intro X Y e hX U f hf
    exact (((ringedDerivedRestriction O U ⋙ H U f).mapIso e).isZero_iff).mp (hX U f hf)
  have hPzero : P (0 : ringedSiteDerived O) := by
    intro U f _
    obtain ⟨s, ht⟩ := (ringedInternalHom_exact (J.over U) (O.over U)).1
      ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (O.over U) (ringedSliceSection O U f)))
    let G := ringedDerivedRestriction O U ⋙ H U f
    exact G.map_isZero (isZero_zero _)
  have hPshift : P.IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro X hX U f hf
    obtain ⟨s, ht⟩ := (ringedInternalHom_exact (J.over U) (O.over U)).1
      ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (O.over U) (ringedSliceSection O U f)))
    let G := ringedDerivedRestriction O U ⋙ H U f
    exact (((G.commShiftIso n).app X).isZero_iff).mpr
      ((shiftFunctor _ n).map_isZero (hX U f hf))
  have hPtri : P.IsTriangulated := by
    refine {
      exists_zero := ⟨0, isZero_zero _, hPzero⟩
      toIsTriangulatedClosed₂ := .mk' ?_ }
    intro T hT h₁ h₃ U f hf
    obtain ⟨s, ht⟩ := (ringedInternalHom_exact (J.over U) (O.over U)).1
      ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (O.over U) (ringedSliceSection O U f)))
    let G := ringedDerivedRestriction O U ⋙ H U f
    exact Pretriangulated.Triangle.isZero₂_of_isZero₁₃ _ (G.map_distinguished T hT)
      (h₁ U f hf) (h₃ U f hf)
  obtain ⟨D, hc, hb, _, hn⟩ := ringedKoszulCompletionReflector O r b I ι hgen
  let η : 𝟭 (ringedSiteDerived O) ⟶ D.completion :=
    { app := D.unit
      naturality := fun X Y a ↦ (hn X Y a).symm }
  obtain ⟨sD, hD, hη⟩ := exact_reflector P D.completion η hc hb
  exact ⟨D, sD, hD, ⟨η, fun _ ↦ rfl, hη⟩, hPiso, hPtri⟩

end CategoryTheory
