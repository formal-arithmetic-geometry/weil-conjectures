/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.SystemCoinducedAdjunction
import WeilConjectures.CategoryTheory.SystemEvaluationTopos
import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Derived evaluation is a localization

Source: the existing explicit strict-system coinduction and exact localization, Stacks 015F.
(blueprint: lem-coef-semilinear-evaluation-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{r} C] (B : ℕ → Sheaf J CommRingCat.{r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- Evaluation of unbounded derived semilinear systems is a localization at the
morphisms that become isomorphisms at the chosen vertex.

Source: `lem-coef-system-coinduced-adjunction` and Stacks 015F (exact derived localization).
(blueprint: lem-coef-semilinear-evaluation-localization).

Proof: in strict systems, evaluation at n has the exact right adjoint which is zero
below n and restriction of scalars above n. Evaluation of this right adjoint at n
is naturally the identity, by the scalar-restriction unit. Therefore the right
adjoint is fully faithful. Transport this exact adjunction through the equivalence
with modules on the sequence site, whose evaluation comparison is the identity on
sections. Localize both exact functors on unbounded complexes. The ordinary counit
is an isomorphism, hence so is its derived counterpart: exact functoriality identifies
the composite of the derived functors with the derived composite. Thus derived
evaluation again has a fully faithful right adjoint, and the reflective-localization
theorem applies. No coefficient flatness, boundedness or normalized-system assumption
enters this argument. -/
theorem evaluation_isLocalization (n : ℕ) :
    (e.{c, v, r} J B τ n).IsLocalization
      ((MorphismProperty.isomorphisms (D.{c, v, r} J (B n))).inverseImage
        (e.{c, v, r} J B τ n)) := by
  let R := rings J B τ
  let Q := SheafOfModules.strictSystemSequenceEquivalence R
  have : Q.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive R
  have : Q.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive R
  let G := SheafOfModules.SequenceCoinduced.rightExtension R n
  have : G.Additive := SheafOfModules.SequenceCoinduced.rightExtension_additive R n
  have := evaluationAdditive.{c, v, r} J B τ n
  have := evaluationLimits.{c, v, r} J B τ n
  have := evaluationColimits.{c, v, r} J B τ n
  let adj₀ := SheafOfModules.SequenceCoinduced.adjunction R n
  let γ : G ⋙ SheafOfModules.systemEvaluation R n ≅ 𝟭 _ :=
    SheafOfModules.SequenceCoinduced.rightExtension_above R n (Nat.le_refl n) ≪≫
      SheafOfModules.systemScalarRestrictionUnit (R.map (homOfLE (Nat.le_refl n)).op)
        (R.map_id (op n))
  let ff := adj₀.fullyFaithfulROfCompIsoId γ
  have : G.Full := ff.full
  have : G.Faithful := ff.faithful
  have : PreservesFiniteLimits G :=
    (SheafOfModules.SequenceCoinduced.rightExtension_exact R n).1
  have : PreservesFiniteColimits G :=
    (SheafOfModules.SequenceCoinduced.rightExtension_exact R n).2
  let η : Q.inverse ⋙ SheafOfModules.systemEvaluation R n ≅ evaluation J B τ n :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ = (eqToHom (evaluation_ring J B τ n).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  have : (G ⋙ Q.functor).Additive := inferInstance
  have : PreservesFiniteLimits (G ⋙ Q.functor) := inferInstance
  have : PreservesFiniteColimits (G ⋙ Q.functor) := inferInstance
  let adj : evaluation J B τ n ⊣ G ⋙ Q.functor :=
    (Q.symm.toAdjunction.comp adj₀).ofNatIsoLeft η
  let δ : (G ⋙ Q.functor) ⋙ evaluation J B τ n ≅ 𝟭 _ := asIso adj.counit
  let da := adj.mapExactDerivedCategory
  let df := da.fullyFaithfulROfCompIsoId
    ((Functor.mapDerivedCategoryCompIso (G ⋙ Q.functor) (evaluation J B τ n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso δ ≪≫ Functor.mapDerivedCategoryIdIso _)
  have := df.full
  have := df.faithful
  exact da.isLocalization

end WeilConjectures.SemilinearSections
