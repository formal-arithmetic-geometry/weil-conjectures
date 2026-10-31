/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ProEtaleFinitePushforwardExact
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition

/-! # Finite-etale direct image of lisse condensed modules

Source: current blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-correction,
prop-fd-zero-extension-comparison.proof.md, Step 3 (and its degree-zero use in Step 2).
(blueprint: lem-fd-condensed-finite-etale-lisse-pushforward).

The single-degree comparison is the canonical right-derived unit, whose inverse is the
asserted derived isomorphism. The split-cover comparison is the biproduct lift of the
pullback-composition and adjunction-counit maps. No choice of an abstract isomorphism
replaces either canonical comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures.FiniteFieldDatum

/-- The map on geometric fibres is the map of the existing base-change functor.
Source: current blueprint, prop-fd-zero-extension-comparison.proof.md, Steps 2--3.
(blueprint: lem-fd-condensed-finite-etale-lisse-pushforward). -/
abbrev geometricFiberMap (D : WeilConjectures.FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (π₀ : X₀ ⟶ Y₀) :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map π₀).left

end WeilConjectures.FiniteFieldDatum

namespace AlgebraicGeometry.ProEtale.CondensedRing

section

attribute [local irreducible] upperStarComp upperStarLowerStarAdjunction

private theorem biproductLift_isIso_of_product
    {A : Type*} [Category* A] [HasZeroMorphisms A]
    {J : Type*} {N : J → A} [HasBiproduct N] {P : A} (a : ∀ j, P ⟶ N j)
    (h : IsIso (Pi.lift a)) : IsIso (biproduct.lift a) := by
  have : IsIso (Pi.lift a) := h
  have he : biproduct.lift a = Pi.lift a ≫ (biproduct.isoProduct N).inv := by
    apply biproduct.hom_ext
    intro j
    simp only [biproduct.isoProduct_inv, Category.assoc, biproduct.lift_π, Pi.lift_π]
  rw [he]
  infer_instance

private theorem singleUnit_isIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    [IsIso F.rightDerivedFunctorUnit] (M : A) : IsIso (F.rightDerivedSingleUnit M) := by
  dsimp only [Functor.rightDerivedSingleUnit]
  infer_instance

private theorem exists_split_sections_allow_empty
    {X U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (y : Y), Etale g ∧ g y = x ∧
      ∃ (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g),
        Nonempty (IsColimit (Cofan.mk (pullback p g)
          (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))) := by
  classical
  obtain ⟨Y, g, y, hg, hy, J, V, ι, hJ, ⟨hc⟩, hi, he⟩ :=
    finite_etale_etale_local_split p x
  let _ := hg
  let _ := hJ
  let _ := Fintype.ofFinite J
  choose e he using he
  let n := Fintype.card J
  let q : Fin n ≃ J := (Fintype.equivFin J).symm
  let b (k : Fin n) : Y ⟶ pullback p g := (e (q k)).inv ≫ ι (q k)
  have hb (k : Fin n) : b k ≫ pullback.snd p g = 𝟙 Y := by
    dsimp [b]
    rw [Category.assoc, ← he, Iso.inv_hom_id]
  let t (k : Fin n) := b k ≫ pullback.fst p g
  have w (k : Fin n) : t k ≫ p = g := by
    dsimp [t]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hb, Category.id_comp]
  have hlift (k : Fin n) :
      pullback.lift (t k) (𝟙 Y) (by simpa using w k) = b k := by
    apply pullback.hom_ext <;> simp [t, hb]
  have hbcol : IsColimit (Cofan.mk (pullback p g) b) := by
    let K (c : Cofan (fun _ : Fin n ↦ Y)) : Cofan V :=
      Cofan.mk c.pt (fun j ↦ (e j).hom ≫ c.inj (q.symm j))
    refine Cofan.IsColimit.mk _ (fun c ↦ hc.desc (K c)) ?_ ?_
    · intro c k
      dsimp [b]
      have hf := hc.fac (K c) ⟨q k⟩
      change ι (q k) ≫ hc.desc (K c) = (e (q k)).hom ≫ c.inj _ at hf
      rw [Category.assoc, hf]
      simp
    · intro c m hm
      apply hc.hom_ext
      rintro ⟨j⟩
      change ι j ≫ m = ι j ≫ hc.desc (K c)
      have hf := hc.fac (K c) ⟨j⟩
      change ι j ≫ hc.desc (K c) = (e j).hom ≫ c.inj (q.symm j) at hf
      rw [hf]
      have h := hm (q.symm j)
      change ((e (q (q.symm j))).inv ≫ ι (q (q.symm j))) ≫ m = _ at h
      rw [q.apply_symm_apply] at h
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        congrArg (fun z ↦ (e j).hom ≫ z) h
  refine ⟨Y, g, y, hg, hy, n, t, w, ?_⟩
  simpa only [hlift] using (show Nonempty (IsColimit (Cofan.mk _ b)) from ⟨hbcol⟩)

private theorem exists_etale_cover_property
    {X : Scheme.{u}} (Q : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop)
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (y : Y),
      Etale g ∧ g y = x ∧ Q Y g) :
    ∃ C : Scheme.Cover.{u} Scheme.etalePrecoverage X,
      ∀ i : C.I₀, Q (C.X i) (C.f i) := by
  classical
  choose Y g y hg hy hQ using h
  exact ⟨Scheme.Cover.mkOfCovers X Y g (fun x ↦ ⟨x, y x, hy x⟩) hg, hQ⟩

private theorem etaleCover_has_proetale_property
    {X : Scheme.{u}} (C : Scheme.Cover.{u} Scheme.etalePrecoverage X)
    (Q : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop)
    (hQ : ∀ i : C.I₀, Q (C.X i) (C.f i)) :
    ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ i : D.I₀, Q (D.X i) (D.f i) :=
  ⟨C.weaken Scheme.etalePrecoverage_le_proetalePrecoverage, hQ⟩

private theorem lisse_pushforward_of_split_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (C : Scheme.Cover.{u} Scheme.etalePrecoverage Y)
    (hC : ∀ i : C.I₀, ∃ (n : ℕ) (t : Fin n → (C.X i ⟶ X))
      (w : ∀ j, t j ≫ p = C.f i),
      Nonempty (IsColimit (Cofan.mk (pullback p (C.f i))
        (fun j ↦ pullback.lift (t j) (𝟙 (C.X i)) (by simpa using w j)))))
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hL : IsLisseCoefficientModule Λ L) :
    IsLisseCoefficientModule Λ ((lowerStar Λ p).obj L) := by
  have hQ (i : C.I₀) : LocFree Λ (C.X i)
      ((upperStar Λ (C.f i)).obj ((lowerStar Λ p).obj L)) := by
    obtain ⟨n, t, w, hc⟩ := hC i
    have : Etale (C.f i) := C.map_prop i
    obtain ⟨ε, _⟩ := localProductComparison Λ p (C.f i) n t w hc
    exact locFree_push_of_comparison Λ p (C.f i) n t L (ε L) hL
  obtain ⟨D, hD⟩ := etaleCover_has_proetale_property C
    (fun Y g ↦ LocFree Λ Y ((upperStar Λ g).obj ((lowerStar Λ p).obj L))) hQ
  exact locFree_of_cover _ D hD


private theorem finiteEtale_lisse_pushforward
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}}
    (p : U ⟶ X) [IsFinite p] [Etale p] :
    (PreservesFiniteLimits (lowerStar Λ p) ∧
      PreservesFiniteColimits (lowerStar Λ p)) ∧
    (∀ L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj Λ U),
      IsLisseCoefficientModule Λ L →
      IsLisseCoefficientModule Λ
          ((lowerStar Λ p).obj L) ∧
        IsIso ((lowerStar Λ p).rightDerivedSingleUnit L)) ∧
    ∃ C : Scheme.Cover.{u} Scheme.etalePrecoverage X,
      ∀ i : C.I₀, ∃ (n : ℕ) (t : Fin n → (C.X i ⟶ U))
        (w : ∀ j, t j ≫ p = C.f i),
        Nonempty (IsColimit (Cofan.mk (pullback p (C.f i))
          (fun j ↦ pullback.lift (t j) (𝟙 (C.X i)) (by simpa using w j)))) ∧
        ∀ L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
            (condensedRingObj Λ U),
          IsLisseCoefficientModule Λ L →
          IsIso (biproduct.lift (fun j ↦
            ((eqToIso (congrArg (upperStar Λ) (w j))).symm ≪≫
              upperStarComp Λ (t j) p).hom.app
                  ((lowerStar Λ p).obj L) ≫
            (upperStar Λ (t j)).map
              ((upperStarLowerStarAdjunction Λ p).counit.app L))) := by
  classical
  obtain ⟨hlim, hcol, hunit, _⟩ := (finitePushforward_exact p).2 Λ
  have : IsIso (lowerStar Λ p).rightDerivedFunctorUnit := hunit
  obtain ⟨C, hC⟩ := exists_etale_cover_property
    (fun Y g ↦ ∃ (n : ℕ) (t : Fin n → (Y ⟶ U))
      (w : ∀ j, t j ≫ p = g),
      Nonempty (IsColimit (Cofan.mk (pullback p g)
        (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))))
    (exists_split_sections_allow_empty p)
  refine ⟨⟨hlim, hcol⟩, ?_, C, ?_⟩
  · intro L hL
    constructor
    · exact lisse_pushforward_of_split_cover Λ p C hC L hL
    · exact singleUnit_isIso (lowerStar Λ p) L
  · intro x
    obtain ⟨n, t, w, hc⟩ := hC x
    refine ⟨n, t, w, hc, ?_⟩
    intro L _
    have : Etale (C.f x) := C.map_prop x
    have hproduct := splitProEtaleModuleProductMap_isIso Λ p (C.f x) n t w hc L
    exact biproductLift_isIso_of_product _ hproduct

end

attribute [local irreducible] upperStarComp upperStarLowerStarAdjunction

/-- Finite-etale direct image is exact, preserves lissity, and is computed in degree zero
by its canonical derived unit. Etale locally, it is the finite sum of the sheet pullbacks.
Source: current blueprint, prop-fd-zero-extension-comparison.proof.md, Steps 2--3;
Stacks Tags 04HN, 095B, 098B; Bhatt--Scholze, Lemma 6.1.17.
(blueprint: lem-fd-condensed-finite-etale-lisse-pushforward).

Proof. (1) Base change preserves finiteness and etaleness (overPullbackMap). Apply
finite_etale_etale_local_split at all target points and enumerate each finite sheet set
by Fin n, allowing n = 0; the sheet maps lift to a coproduct cofan of the pullback.
These etale neighbourhoods form an etale cover (Scheme.Cover.mkOfCovers).
(2) Apply clause (2) of lem-fd-proetale-finite-pushforward-exact (finitePushforward_exact)
to the finite etale map and the condensed coefficient ring. It gives exactness on
internal modules and invertibility of the ordinary unbounded right-derived unit; hence
rightDerivedSingleUnit, the derived image of the inverse single-complex comparison
followed by a component of that unit, is invertible at every L.
(3) Apply splitProEtaleModuleProductMap_isIso to each splitting cofan. Its components
are the pullback compositor followed by the pulled-back adjunction counit, exactly
the displayed biproduct lift; the biproduct lift is the product lift followed by the
inverse biproduct-to-product isomorphism, so it is invertible, including n = 0.
(4) IsLisseCoefficientModule is the normalized LocFree predicate of
lem-weil-pbc-finite-etale-locally-free-models. On each splitting neighbourhood, its
proved helpers localProductComparison and locFree_push_of_comparison identify the
restriction of pi_* L with the finite product of the sheet pullbacks of L, which is
locally finite free (common refinement of the finitely many covers, finite sums of
free modules). Weaken the etale splitting cover to a pro-etale cover (Tag 098B) and
apply locFree_of_cover. The ranks may vary; empty sheet sets, empty schemes and
L = 0 give rank zero without any nonemptiness assumption. -/
theorem condensedFiniteEtale_lisse_pushforward
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (π₀ : X₀ ⟶ Y₀) [IsFinite π₀.left] [Etale π₀.left] :
    (PreservesFiniteLimits (lowerStar (Profinite.padicAlgClRingObj ℓ)
        (D.geometricFiberMap π₀)) ∧
      PreservesFiniteColimits (lowerStar (Profinite.padicAlgClRingObj ℓ)
        (D.geometricFiberMap π₀))) ∧
    (∀ L : Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber X₀).left) Ab.{u + 1})
        (padicAlgClRingObj (D.geometricFiber X₀).left ℓ),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ)
          ((lowerStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFiberMap π₀)).obj L) ∧
        IsIso ((lowerStar (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiberMap π₀)).rightDerivedSingleUnit L)) ∧
    ∃ C : Scheme.Cover.{u} Scheme.etalePrecoverage (D.geometricFiber Y₀).left,
      ∀ i : C.I₀, ∃ (n : ℕ) (t : Fin n → (C.X i ⟶ (D.geometricFiber X₀).left))
        (w : ∀ j, t j ≫ D.geometricFiberMap π₀ = C.f i),
        Nonempty (IsColimit (Cofan.mk (pullback (D.geometricFiberMap π₀) (C.f i))
          (fun j ↦ pullback.lift (t j) (𝟙 (C.X i)) (by simpa using w j)))) ∧
        ∀ L : Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber X₀).left) Ab.{u + 1})
            (padicAlgClRingObj (D.geometricFiber X₀).left ℓ),
          IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L →
          IsIso (biproduct.lift (fun j ↦
            ((eqToIso (congrArg (upperStar (Profinite.padicAlgClRingObj ℓ)) (w j))).symm ≪≫
              upperStarComp (Profinite.padicAlgClRingObj ℓ) (t j)
                (D.geometricFiberMap π₀)).hom.app
                  ((lowerStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFiberMap π₀)).obj L) ≫
            (upperStar (Profinite.padicAlgClRingObj ℓ) (t j)).map
              ((upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
                (D.geometricFiberMap π₀)).counit.app L))) := by
  have _hchar : ℓ ≠ D.p := hℓ
  have : IsFinite (D.geometricFiberMap π₀) :=
    MorphismProperty.overPullbackMap (P := @IsFinite)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) π₀ inferInstance
  have : Etale (D.geometricFiberMap π₀) :=
    MorphismProperty.overPullbackMap (P := @Etale)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) π₀ inferInstance
  exact finiteEtale_lisse_pushforward (Profinite.padicAlgClRingObj ℓ) (D.geometricFiberMap π₀)

end AlgebraicGeometry.ProEtale.CondensedRing
