/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.CategoryTheory.Ringed.RingedScalarTensorMonoidal
import WeilConjectures.SixFunctors.Coefficient.Finite.CoefficientFiniteScalarSection
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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

/-! # Monoidality of the fixed finite coefficient tensor comparison

Source: Stacks 06YY and 07A4.
(blueprint: lem-coef-finite-tensor-monoidal).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionExtension
  coefficientTotalTensor
  coefficientFiniteReductionModel coefficientLocalizedCounitModel

attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  CategoryTheory.uniformProd
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralReductionTargetHasDerivedCategory coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat

-- The cochain presentation uses exactly the recorded homotopy counit.
@[reducible] private noncomputable def finiteCochainModel (n : ℕ) :
    SheafOfModules.DerivedChangeOfRingsCochainModel.{t+1, t, max u (t+1),
      max (t+2) (u+1), max (t+2) (u+1)}
      (completedIntegralCommRingProjectionUnrestricted l E W n) := by
  let A := scalarReductionSource l E W
  let B := normalizedDVRModules l E W n
  let F := scalarReductionExtension l E W n
  let : F.Additive := coefficientFiniteExtensionAdditive l E W n
  let T := coefficientFiniteDerivedExtension l E W n
  let ε := scalarReductionCounit l E W n
  let H := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let : H.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := by
    simpa only [H, F, scalarReductionExtension] using
      (scalarReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose_spec.2.1
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) :=
    (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.1
  let q := HomotopyCategory.quotient A (.up ℤ)
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh H T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ H ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β := Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  have hβ := pointwise_change_iso T i j α hα
  refine
    { E := F
      obj_eq := by
        simpa only [F, scalarReductionExtension] using
          (scalarReductionExistence l E W n).choose_spec.choose
      map_eq := by
        intro M N f
        with_unfolding_all exact
          (scalarReductionExistence l E W n).choose_spec.choose_spec.choose f
      additive := coefficientFiniteExtensionAdditive l E W n
      preserves := by
        intro P Q f hP hQ hf
        simpa only [F, scalarReductionExtension] using
          (scalarReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose_spec.1
            f hP hQ hf
      T := T
      pointwise := ?_
      ε := β
      universal := ⟨hβ.isRightKanExtension⟩
      triangulated :=
        (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.2.1
      computes := ?_ }
  · intro X
    exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
        (HomologicalComplex.quasiIso A (.up ℤ)) X).2
      ((hβ _).hasPointwiseRightKanExtensionAt)
  · intro P hP
    have hcomp : IsIso (ε.app (q.obj P)) :=
      coefficientFiniteReductionCounit_isIso l E W P hP n
    let e := T.mapIso (i.app P).symm ≪≫
      @asIso _ _ _ _ (ε.app (q.obj P)) hcomp ≪≫ j.app P
    have he : β.app P = e.hom := by
      with_unfolding_all
        calc
          β.app P = T.map (i.inv.app P) ≫
              (𝟙 _ ≫ ε.app (q.obj P)) ≫ j.hom.app P := rfl
          _ = T.map (i.inv.app P) ≫ ε.app (q.obj P) ≫ j.hom.app P :=
            congrArg (fun f ↦ T.map (i.inv.app P) ≫ f ≫ j.hom.app P)
              (Category.id_comp (ε.app (q.obj P)))
          _ = e.hom := rfl
    change IsIso (β.app P)
    rw [he]
    infer_instance

end WeilConjectures
