/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementConstruction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import all WeilConjectures.AlgebraicGeometry.RingedCoefficientScalarUnits
import WeilConjectures.AlgebraicGeometry.RingedRefinementGeometricCalculus
import WeilConjectures.AlgebraicGeometry.RingedRefinementScalarComparisons

/-!
# Normalized coefficient and geometric calculus on the actual sites

(blueprint: lem-pur-ringed-refinement-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

namespace ScalarConstruction

open SheafOfModules.SuccessiveDerivedQuotient

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}

private structure Model {R S : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ S)
    extends SuccessiveDerivedQuotient.Presentation.{u + 1, u, u + 1, u + 2} a where
  preserves : ∀ {P Q : CochainComplex (Modules R) ℤ} (f : P ⟶ Q),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := R) Q → QuasiIso f →
    QuasiIso ((ordinary.mapHomologicalComplex (.up ℤ)).map f)
  pointwise : Functor.HasPointwiseLeftDerivedFunctor
    (ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (HomotopyCategory.quasiIso (Modules R) (.up ℤ))
  triangulated : ∃ (_ : derived.CommShift ℤ), derived.IsTriangulated
  computes : ∀ P : CochainComplex (Modules R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      IsIso (counit.app ((HomotopyCategory.quotient _ _).obj P))

private theorem model_exists {R S : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ S) :
    Nonempty (Model a) := by
  obtain ⟨E, he, hm, hadd, hpres, hpw, L, ε, hL, htri, hc⟩ :=
    derivedChangeOfRingsIndependentCoefficients a
  exact ⟨{
    ordinary := E
    obj_eq := he
    map_eq := hm
    additive := hadd
    derived := L
    counit := ε
    universal := hL
    preserves := hpres
    pointwise := hpw
    triangulated := htri
    computes := hc }⟩

private def model {R S : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ S) : Model a :=
  Classical.choice (model_exists a)

private def presentation {R S : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ S) :=
  (model a).toPresentation

private def cochain {R S : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ S) :
    DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} a := by
  let p := model a
  let q := HomotopyCategory.quotient (Modules R) (.up ℤ)
  let F := p.ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let α := (Functor.associator q DerivedCategory.Qh p.derived).hom ≫
    Functor.whiskerLeft q p.counit
  let i := DerivedCategory.quotientCompQhIso (Modules R)
  let j : q ⋙ F ≅ p.ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (p.ordinary.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (Modules S))
  let β := Functor.whiskerRight i.inv p.derived ≫ α ≫ j.hom
  let := p.pointwise
  let := p.universal
  have hα := pointwise_precomp_full q DerivedCategory.Qh F p.derived p.counit
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor p.derived
      p.counit (HomotopyCategory.quasiIso (Modules R) (.up ℤ)))
  have hβ := pointwise_change_iso p.derived i j α hα
  refine {
    E := p.ordinary
    obj_eq := p.obj_eq
    map_eq := p.map_eq
    additive := p.additive
    preserves := p.preserves
    T := p.derived
    pointwise := ?_
    ε := β
    universal := ⟨hβ.isRightKanExtension⟩
    triangulated := p.triangulated
    computes := ?_ }
  · intro X
    exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff
      (p.ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
        (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) X).2
      ((hβ _).hasPointwiseRightKanExtensionAt)
  · intro P hP
    have := p.computes P hP
    dsimp [β, α]
    infer_instance

private theorem cochain_counit {R S : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ) :
    (cochain a).ε.app P = (presentation a).counit.app
      ((HomotopyCategory.quotient _ _).obj P) := by
  dsimp [cochain, presentation]
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors]
  erw [CategoryTheory.Functor.map_id, DerivedCategory.Qh.map_id]
  simp only [Category.id_comp]
  exact Category.comp_id _

private def adjData {R S : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ S) :
    AdjData (presentation a) :=
  Classical.choice (adjData_exists (presentation a))

private def normalization : Normalization (J := J) (@presentation C _ _ J) := by
  let p := @presentation C _ _ J
  let D := @adjData C _ _ J
  let A := fun {R S : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ S) ↦ (D a).ordinary
  exact {
    ordinary := ordinaryComp p A
    ordinary_hom := ordinaryComp_hom p A (fun a ↦ (D a).ordinary_unit)
    ordinary_inv := ordinaryComp_inv p A (fun a ↦ (D a).ordinary_unit)
    derived := derivedComp p D
    computed := fun a ↦ (D a).computed
    intermediate_computed := fun a b ↦ intermediate_computed a b (p a) (p b) (D b)
    representative := fun a b P _ _ ↦ derivedComp_representative p D a b
      ((HomotopyCategory.quotient _ _).obj P)
    ordinaryAdjunction := A
    ordinary_unit := fun a ↦ (D a).ordinary_unit
    right := fun a ↦ (restriction a).mapDerivedCategory
    right_factors := fun a ↦ (restriction a).mapDerivedCategoryFactorsh
    adjunction := fun a ↦ (D a).derived
    adjunction_normalization := fun a ↦ (D a).unit_normalization
    restrictionComp := resComp
    restrictionComp_sections := by intros; rfl
    rightComp := rightComp
    rightComp_normalization := rightComp_normalization
    unit_comp := derivedComp_unit p D
    associative := derivedComp_assoc p D
    coefficient_naturality := derivedComp_coefficient_naturality p D }


private theorem composition_representative
    {R S V : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ S) (b : S ⟶ V)
    (P : CochainComplex (Modules R) ℤ) :
    (normalization.derived a b).hom.app (DerivedCategory.Q.obj P) ≫
        (cochain (a ≫ b)).ε.app P =
      (cochain b).T.map ((cochain a).ε.app P) ≫
        (cochain b).ε.app (((cochain a).E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (normalization.ordinary a b).hom (.up ℤ)).app P) := by
  rw [cochain_counit, cochain_counit, cochain_counit]
  have h := derivedComp_representative (@presentation C _ _ J) (@adjData C _ _ J)
    a b ((HomotopyCategory.quotient _ _).obj P)
  convert h using 1
  · rfl
  · rfl

private def ordinaryUnit (R : Sheaf J CommRingCat.{u + 1}) :
    (cochain (𝟙 R)).E ≅ 𝟭 (Modules R) :=
  RingedCoefficientProjection.ordinaryUnit normalization R

private def derivedUnit (R : Sheaf J CommRingCat.{u + 1}) :
    (cochain (𝟙 R)).T ≅ 𝟭 (DerivedCategory (Modules R)) :=
  RingedCoefficientProjection.derivedUnit normalization R

private theorem unit_representative (R : Sheaf J CommRingCat.{u + 1})
    (P : CochainComplex (Modules R) ℤ) :
    (derivedUnit R).hom.app (DerivedCategory.Q.obj P) =
      (cochain (𝟙 R)).ε.app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ordinaryUnit R).hom (.up ℤ)).app P) := by
  have hc : RingedCoefficientProjection.computation (presentation (𝟙 R)) P =
      (cochain (𝟙 R)).ε.app P := by
    dsimp [RingedCoefficientProjection.computation,
      derivedPullbackComplexComparison, cochain, presentation]
    simp only [Category.id_comp]
  exact hc ▸ RingedCoefficientProjection.derivedUnit_representative normalization R P

private theorem unit_one (R : Sheaf J CommRingCat.{u + 1}) (M : Modules R)
    (Z : Cᵒᵖ) (x : M.val.obj Z) :
    ((ordinaryUnit R).hom.app M).val.app Z
      ((eqToHom ((cochain (𝟙 R)).obj_eq M).symm).val.app Z
        (pure (𝟙 R) M Z 1 x)) = x := by
  exact RingedCoefficientProjection.ordinaryUnit_one normalization R M Z x


private def compOrdinary {R S V : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) {d : R ⟶ V} (h : a ≫ b = d) :
    (cochain a).E ⋙ (cochain b).E ≅ (cochain d).E :=
  normalization.ordinary a b ≪≫ eqToIso (congrArg (fun t ↦ (cochain t).E) h)

private def compDerived {R S V : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) {d : R ⟶ V} (h : a ≫ b = d) :
    (cochain a).T ⋙ (cochain b).T ≅ (cochain d).T :=
  normalization.derived a b ≪≫ eqToIso (congrArg (fun t ↦ (cochain t).T) h)

private theorem compPure {R S V : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) {d : R ⟶ V} (h : a ≫ b = d)
    (M : Modules R) (Z : Cᵒᵖ) (x : M.val.obj Z)
    (y : S.obj.obj Z) (z : V.obj.obj Z) :
    HEq (((compOrdinary a b h).hom.app M).val.app Z
      ((eqToHom ((cochain b).obj_eq ((cochain a).E.obj M)).symm).val.app Z
        (pure b ((cochain a).E.obj M) Z z
          ((eqToHom ((cochain a).obj_eq M).symm).val.app Z (pure a M Z y x)))))
      ((eqToHom ((cochain d).obj_eq M).symm).val.app Z
        (pure d M Z (b.hom.app Z y * z) x)) := by
  subst d
  apply heq_of_eq
  simp only [compOrdinary, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id]
  convert normalization.ordinary_hom a b M Z x y z using 1 <;>
    (dsimp [cochain, presentation, SuccessiveDerivedQuotient.sectionTensor])

private theorem compRepresentative {R S V : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) {d : R ⟶ V} (h : a ≫ b = d)
    (P : CochainComplex (Modules R) ℤ) :
    (compDerived a b h).hom.app (DerivedCategory.Q.obj P) ≫ (cochain d).ε.app P =
      (cochain b).T.map ((cochain a).ε.app P) ≫
        (cochain b).ε.app (((cochain a).E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (compOrdinary a b h).hom (.up ℤ)).app P) := by
  subst d
  simpa only [compDerived, compOrdinary, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    NatTrans.comp_id, NatTrans.comp_app, NatTrans.id_app, Category.comp_id] using
      composition_representative a b P

private def identityOrdinary {R : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ R) (h : a = 𝟙 R) : (cochain a).E ≅ 𝟭 (Modules R) :=
  eqToIso (congrArg (fun t ↦ (cochain t).E) h) ≪≫ ordinaryUnit R

private def identityDerived {R : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ R) (h : a = 𝟙 R) : (cochain a).T ≅ 𝟭 (DerivedCategory (Modules R)) :=
  eqToIso (congrArg (fun t ↦ (cochain t).T) h) ≪≫ derivedUnit R

private theorem identityPure {R : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ R) (h : a = 𝟙 R) (M : Modules R) (Z : Cᵒᵖ) (x : M.val.obj Z) :
    ((identityOrdinary a h).hom.app M).val.app Z
      ((eqToHom ((cochain a).obj_eq M).symm).val.app Z (pure a M Z 1 x)) = x := by
  subst a
  simpa only [identityOrdinary, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.id_comp] using unit_one R M Z x

private theorem identityRepresentative {R : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ R) (h : a = 𝟙 R) (P : CochainComplex (Modules R) ℤ) :
    (identityDerived a h).hom.app (DerivedCategory.Q.obj P) =
      (cochain a).ε.app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (identityOrdinary a h).hom (.up ℤ)).app P) := by
  subst a
  simpa only [identityOrdinary, identityDerived, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.id_comp] using unit_representative R P

end ScalarConstruction

private theorem scalarFamily_exists (m : Mode) (T : Scheme.{u}) (c : Coefficients m T) :
    ∃ s : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B),
      DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
        ((c.rings W).map a),
      ∀ o : Calculus c, o.scalar = s → Nonempty (ScalarComposition o) := by
  let s := fun (W : Over T) {A B : Rings m T} (a : A ⟶ B) ↦
    ScalarConstruction.cochain ((c.rings W).map a)
  refine ⟨s, ?_⟩
  rintro ⟨op, cf, om, scalar⟩ h
  dsimp only at h
  subst scalar
  refine ⟨{
    ordinary := fun W {A B C} a b ↦
      ScalarConstruction.compOrdinary _ _ ((c.rings W).map_comp a b).symm
    pure := fun W {A B C} a b M Z x y z ↦ ScalarConstruction.compPure _ _
      ((c.rings W).map_comp a b).symm M Z x y z
    derived := fun W {A B C} a b ↦
      ScalarConstruction.compDerived _ _ ((c.rings W).map_comp a b).symm
    representative := fun W {A B C} a b P _ ↦ ScalarConstruction.compRepresentative _ _
      ((c.rings W).map_comp a b).symm P
    ordinaryUnit := fun W A ↦ ScalarConstruction.identityOrdinary _ ((c.rings W).map_id A)
    unit_pure := fun W A M Z x ↦ ScalarConstruction.identityPure _
      ((c.rings W).map_id A) M Z x
    unit := fun W A ↦ ScalarConstruction.identityDerived _ ((c.rings W).map_id A)
    unit_representative := fun W A P _ ↦ ScalarConstruction.identityRepresentative _
      ((c.rings W).map_id A) P }⟩


-- Preserve the existing existential binder names, even though later fields do not use them.
set_option linter.unusedVariables false in
/-- Geometric and scalar operations, before the clopen comparisons and their laws.
Source: Stacks 03D7, 06YY, 07A6; coefficient supplement Steps 1--2 and 6
(blueprint: lem-pur-ringed-refinement-core).
Proof: construct module inverse image as the left adjoint of sectionwise direct
image with the structural map obtained from the ring inverse-image compositor.
The coefficient identification after inverse image is an isomorphism, so
inverse image is exact. Module
sheaf categories are Grothendieck and have K-injective resolutions. For an open,
transport the direct-sum extension and sheafification adjunction from the localized
site; its unit is an isomorphism and extension is exact. Take each scalar universal
pair from derived change of rings. Direct-image compositors are induced on every
section by fibre-product associativity; their conjugates fix inverse-image ones.
Restriction of scalars commutes with direct image by the identity on underlying
sections; taking left mates fixes the ordinary scalar comparison. Its K-flat
localization gives the pull comparison. The open-unit transpose gives delta,
invertible by the normalized open tensor comparison. Balanced tensor associativity
and the unit are localized on K-flat representatives to give ScalarComposition.
All constructions apply on the vertical sites with unchanged coefficient index. -/
theorem ringedRefinementCore (m : Mode) (T : Scheme.{u}) :
    ∃ (o : Calculus (canonicalCoefficients m T)) (p : Spatial o)
      (sc : ScalarComparisons o), Nonempty (ScalarComposition o) := by
  obtain ⟨s, hs⟩ := scalarFamily_exists m T (canonicalCoefficients m T)
  obtain ⟨o, p, ho⟩ := geometricCalculus_exists m T s
  obtain ⟨sc⟩ := scalarComparisons_exists m T o
  exact ⟨o, p, sc, hs o ho⟩

end SheafOfModules.RingedRefinement
