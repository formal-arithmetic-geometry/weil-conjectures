/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Finite-dimensional actual fibres of lisse condensed coefficient modules

Source: current blueprint, sec-deligne-laumon-general,
sk-lem-wgen-punctual-cutoff/lem-zl-mixed-punctual-cutoff.proof.md, paragraph 3;
Bhatt--Scholze, Example 4.1.10; Stacks Project, Tag 03DO.
(blueprint: lem-zl-condensed-lisse-fibres-finite)

The coefficient ring is the bounded finite-subextension-valued condensed algebraic closure.
The existing field evaluation supplies global sections with their constant-section scalar action.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem evaluated_finite_biproduct
    {C : Type v} [Category.{w} C] [Preadditive C] [HasFiniteBiproducts C]
    {R : Type u} [Field R] (F : C ⥤ ModuleCat.{z} R)
    [F.Additive] [PreservesFiniteColimits F]
    (A M : C) (r : ℕ) (e : M ≅ ⨁ fun _ : Fin r ↦ A)
    (c : F.obj A ≃ₗ[R] R) :
    FiniteDimensional R (F.obj M) ∧ Nonempty (F.obj M ≃ₗ[R] (Fin r → R)) := by
  let eV : F.obj M ≅ ModuleCat.of R (Fin r → F.obj A) :=
    F.mapIso e ≪≫ F.mapBiproduct (fun _ : Fin r ↦ A) ≪≫
      ModuleCat.biproductIsoPi (fun _ : Fin r ↦ F.obj A)
  let d : F.obj M ≃ₗ[R] (Fin r → R) :=
    eV.toLinearEquiv.trans (LinearEquiv.piCongrRight fun _ : Fin r ↦ c)
  exact ⟨LinearEquiv.finiteDimensional d.symm, ⟨d⟩⟩

/-- The actual fibre of a lisse condensed algebraic-closure coefficient module is finite
free, and its global sections are finite dimensional over the coefficient field.
Source: current blueprint lem-zl-mixed-punctual-cutoff.proof.md, paragraph 3;
Bhatt--Scholze, Example 4.1.10; Stacks Project, Tag 03DO
(blueprint: lem-zl-condensed-lisse-fibres-finite).

Proof: (1) The lisse predicate gives a pro-etale cover of S and finite-free
trivializations for the actual module inverse image along each covering map.
The algebraically closed point b lifts through some member: pull the cover back
to Spec k, choose a nonempty member, and split its weakly etale projection.
(2) Pull that member's trivialization back along the lift. The pullback is additive
and sends the regular module to the regular module, hence preserves finite freeness. Transport this
along the module inverse-image composition comparison and choose its finite rank r.
(3) The constructed field evaluation is additive and preserves finite colimits.
Its finite-biproduct comparison, followed by the regular-module coordinates,
therefore gives a linear isomorphism from the evaluated fibre to the r-fold
power of PadicAlgCl ell. Transport finite dimensionality through its inverse.
For r = 0 the biproduct is zero and the function space has empty index set. -/
theorem condensedLisse_fibres_finite
    (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S))
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L)
    (b : Spec (.of k) ⟶ S) (hb : b ≫ (S ↘ Spec (.of k)) = 𝟙 _) :
    FiniteDimensional (PadicAlgCl ℓ)
      ((CondensedQbarGeometricEvaluation.fieldFiber k ℓ).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj L)) ∧
    ∃ r : ℕ,
      Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj L ≅
        Mod.finiteFree
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))) r) ∧
      Nonempty (((CondensedQbarGeometricEvaluation.fieldFiber k ℓ).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj L)) ≃ₗ[PadicAlgCl ℓ]
          (Fin r → PadicAlgCl ℓ)) := by
  have _ := hℓp
  obtain ⟨𝒰, h𝒰⟩ := hL
  obtain ⟨i, g, hg⟩ := 𝒰.exists_comp_eq_of_isSepClosed_of_proetale b
  subst b
  have hfree := (h𝒰 i).map
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g)
    (CondensedRing.upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) g)
  have hcomp := hfree.of_iso
    ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ℓ) g (𝒰.f i)).app L).symm
  obtain ⟨r, ⟨eM⟩⟩ := hcomp
  let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))
  let F := CondensedQbarGeometricEvaluation.fieldFiber k ℓ
  obtain ⟨hfin, hcoord⟩ := evaluated_finite_biproduct F (Mod.regular A)
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (g ≫ 𝒰.f i)).obj L) r eM
    (CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ℓ)
  exact ⟨hfin, r, ⟨eM⟩, hcoord⟩

end AlgebraicGeometry.ProEtale
