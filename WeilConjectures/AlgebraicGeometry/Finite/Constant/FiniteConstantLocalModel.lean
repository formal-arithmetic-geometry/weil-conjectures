/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Field.ULift
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
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
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
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
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
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
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
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
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel

/-!
# Finite constant local models for condensed coefficients

Source: blueprint main-20261015, `sk-def-sfb-constructible-local-model.md`
(blueprint: det-def-sfb-constructible-local-model).

Scalars are encoded as a ring object of abelian groups, and scalar modules as internal
modules in abelian groups. These are precisely ordinary modules over the scalar ring.
The constant sheaf on the profinite point is formed before inverse image to a scheme;
only this constant sheaf, rather than an arbitrary condensed module, is called constant.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Sections at the one-point profinite set. Source: blueprint local-model definition,
first paragraph (blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarSections :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  (sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
    (op (Profinite.of PUnit.{u + 1}))

/-- The sections functor has the lax monoidal structure right adjoint to the monoidal
constant sheaf functor. Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable instance scalarSections_laxMonoidal : scalarSections.{u}.LaxMonoidal :=
  (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit).rightAdjointLaxMonoidal

@[instance_reducible]
private noncomputable def constantScalarSheaf_laxBraided :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).LaxBraided := by
  let : (Functor.const Profinite.{u}ᵒᵖ :
      Ab.{u + 1} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}).LaxBraided :=
    { braided := by intros; ext; simp [Functor.LaxMonoidal.μ]; rfl }
  exact inferInstanceAs (Functor.const Profinite.{u}ᵒᵖ ⋙
    presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).LaxBraided

@[instance_reducible]
private noncomputable def scalarSections_laxBraided : scalarSections.{u}.LaxBraided := by
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let : F.LaxBraided := constantScalarSheaf_laxBraided
  let : F.Braided := { toMonoidal := inferInstance, braided := Functor.LaxBraided.braided }
  let adj : F ⊣ scalarSections.{u} := constantSheafAdj
    (coherentTopology Profinite.{u}) Ab.{u + 1} Profinite.isTerminalPUnit
  refine { toLaxMonoidal := scalarSections_laxMonoidal, braided := ?_ }
  intro A B
  change adj.homEquiv _ _ _ ≫ scalarSections.map (β_ A B).hom =
    (β_ _ _).hom ≫ adj.homEquiv _ _ _
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  rw [Functor.map_braiding]
  dsimp only [F]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [BraidedCategory.braiding_naturality]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]

/-- The scalar ring Λ(*), encoded as a ring object of abelian groups. Its underlying
abelian group is literally evaluation at *. Source: blueprint local-model definition,
first paragraph (blueprint: det-def-sfb-constructible-local-model). -/
noncomputable abbrev scalarRingObj : Ab.{u + 1} := scalarSections.obj Λ

/-- The scalar ring is commutative. Source: blueprint local-model proof, Step 1.
Proof: evaluation's multiplication is induced from the sheaf tensor comparison; the
symmetry and the commutativity of Λ give commutativity on sections.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarRingObj_comm : IsCommMonObj (scalarRingObj Λ) := by
  let := scalarSections_laxBraided.{u}
  exact Functor.isCommMonObj_obj (F := scalarSections.{u}) (M := Λ)

attribute [instance] scalarRingObj_comm

/-- Sheafified constant abelian groups pulled to X. This is the constant-sheaf functor
on X: inverse image preserves colimits and the integer tensor unit, hence preserves
constant abelian sheaves, which are presentations by coproducts of that unit.
Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarConstant (X : Scheme.{u}) :
    Ab.{u + 1} ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint X

/-- The constant-sheaf construction followed by inverse image is monoidal.
Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable instance scalarConstant_monoidal (X : Scheme.{u}) :
    (scalarConstant X).Monoidal :=
  inferInstanceAs (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
    upperStarFromPoint X).Monoidal

/-- The scalar map R_X → Λ_X is the inverse image of the constant-sheaf counit at Λ.
Thus a scalar is pulled back from Λ(*) rather than chosen in Γ(X,Λ_X).
Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarCoefficientHom (X : Scheme.{u}) :
    (scalarConstant X).obj (scalarRingObj Λ) ⟶ condensedRingObj Λ X :=
  (upperStarFromPoint X).map
    ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app Λ)

/-- The scalar map preserves multiplication and unit. Source: blueprint local-model
proof, Step 1. Proof: the constant-sheaf adjunction is monoidal, so its counit is a
ring morphism, and the monoidal inverse image preserves ring morphisms.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarCoefficientHom_isMonHom (X : Scheme.{u}) :
    IsMonHom (scalarCoefficientHom Λ X) := by
  let _ := ‹IsCommMonObj Λ›
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let G := (sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
    (op (Profinite.of PUnit.{u + 1}))
  let : G.LaxMonoidal := scalarSections_laxMonoidal
  let adj : F ⊣ G := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  have : adj.IsMonoidal := inferInstance
  have hc : @IsMonHom _ _ _ (F.obj (G.obj Λ)) Λ
      (F.monObjObj (G.obj Λ)) ‹MonObj Λ› (adj.counit.app Λ) :=
    adj.isMonHom_counitAlgHom Λ
  have hm : @IsMonHom _ _ _ ((upperStarFromPoint X).obj (F.obj (G.obj Λ)))
      ((upperStarFromPoint X).obj Λ)
      ((upperStarFromPoint X).monObjObj (F.obj (G.obj Λ)))
      ((upperStarFromPoint X).monObjObj Λ)
      ((upperStarFromPoint X).map (adj.counit.app Λ)) :=
    Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _ _
  dsimp only [scalarConstant_monoidal, scalarConstant]
  exact IsMonHom.of_eq
    (h₁ := (upperStarFromPoint X).monObjObj (F.obj (G.obj Λ)))
    (h₂ := (upperStarFromPoint X).monObjObj Λ) (scalarCoefficientHom Λ X)
    (Functor.monObjObj_comp F (upperStarFromPoint X) (G.obj Λ)).symm rfl (hf := hm)

attribute [instance] scalarCoefficientHom_isMonHom

/-- The constant scalar ring on X is commutative. Source: blueprint local-model proof,
Step 1. Proof: the constant presheaf functor, sheafification and inverse image are
symmetric monoidal and transport commutative ring objects to commutative ring objects.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarConstant_comm (X : Scheme.{u}) :
    IsCommMonObj ((scalarConstant X).obj (scalarRingObj Λ)) := by
  dsimp only [scalarConstant_monoidal, scalarConstant]
  let := constantScalarSheaf_laxBraided.{u}
  change IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
    upperStarFromPoint X).obj (scalarRingObj Λ))
  infer_instance

attribute [instance] scalarConstant_comm

/-- E_X(P) = Λ_X ⊗_{R_X} P_X, using actual scalar extension along the canonical map.
This functor starts with ordinary scalar modules and takes values in module sheaves.
Source: blueprint local-model definition and proof, Steps 1–2
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def finiteConstantScalarExtension (X : Scheme.{u}) :
    Mod Ab.{u + 1} (scalarRingObj Λ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (scalarConstant X).mapMod (scalarRingObj Λ) ⋙ Mod.extendScalars (scalarCoefficientHom Λ X)

/-- A scalar section on X, with the unit comparison included explicitly.
Source: blueprint local-model proof, Steps 1–2
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarSection (X : Scheme.{u}) (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ condensedRingObj Λ X :=
  Functor.LaxMonoidal.ε (scalarConstant X) ≫
    (scalarConstant X).map a ≫ scalarCoefficientHom Λ X

/-- The finite matrix with scalar entries, acting on finite free Λ_X-modules.
The first index is the source column and the second is the target row.
A map ℤ → Λ(*) encodes its value at 1, so these entries are exactly elements of Λ(*).
Source: blueprint local-model definition, Lemma (2), and proof, Step 2
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarMatrix (X : Scheme.{u}) {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    Mod.finiteFree (condensedRingObj Λ X) m ⟶
      Mod.finiteFree (condensedRingObj Λ X) n :=
  biproduct.matrix fun j k ↦
    Mod.regularLift (Mod.regular (condensedRingObj Λ X)) (scalarSection Λ X (A j k))

private noncomputable def scalarRegularIso (X : Scheme.{u}) :
    (finiteConstantScalarExtension Λ X).obj (Mod.regular (scalarRingObj Λ)) ≅
      Mod.regular (condensedRingObj Λ X) :=
  (Mod.extendScalars (scalarCoefficientHom Λ X)).mapIso
      (Mod.isoMk (Iso.refl _) (by simp)) ≪≫
    Mod.regularExtensionIso (scalarCoefficientHom Λ X)

private theorem scalarRegular_entry (X : Scheme.{u})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    (finiteConstantScalarExtension Λ X).map
        (Mod.regularLift (Mod.regular (scalarRingObj Λ)) a) ≫
      (scalarRegularIso Λ X).hom =
    (scalarRegularIso Λ X).hom ≫
      Mod.regularLift (Mod.regular (condensedRingObj Λ X)) (scalarSection Λ X a) := by
  let F := scalarConstant X
  let R := scalarRingObj Λ
  let S := condensedRingObj Λ X
  let φ := scalarCoefficientHom Λ X
  have hm : (F.mapMod R).map (Mod.regularLift (Mod.regular R) a) ≫
      (Mod.isoMk (Iso.refl _) (by simp) :
        (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R)).hom =
      (Mod.isoMk (Iso.refl _) (by simp) :
        (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R)).hom ≫
      Mod.regularLift (Mod.regular (F.obj R)) (Functor.LaxMonoidal.ε F ≫ F.map a) := by
    apply Mod.regular_hom_ext
    change (MonObj.one : 𝟙_ _ ⟶ F.obj R) ≫
        (F.map (Mod.regularLift (Mod.regular R) a).hom ≫ 𝟙 _) =
      (MonObj.one : 𝟙_ _ ⟶ F.obj R) ≫ (𝟙 _ ≫ _)
    simp only [Category.comp_id, Category.id_comp]
    rw [Mod.one_comp_regularLift, Functor.obj.η_def, Category.assoc,
      ← F.map_comp, Mod.one_comp_regularLift]
  have h : Mod.regularLift (Mod.regular (F.obj R))
        (Functor.LaxMonoidal.ε F ≫ F.map a) ≫ Mod.regularCoefficientMap φ =
      Mod.regularCoefficientMap φ ≫ (Mod.comap φ).map
        (Mod.regularLift (Mod.regular S) (scalarSection Λ X a)) := by
    apply Mod.regular_hom_ext
    change MonObj.one ≫ (_ ≫ φ) = MonObj.one ≫ (φ ≫ _)
    change (MonObj.one : 𝟙_ _ ⟶ F.obj R) ≫
        ((Mod.regularLift (Mod.regular (F.obj R))
          (Functor.LaxMonoidal.ε F ≫ F.map a)).hom ≫ φ) =
      (MonObj.one : 𝟙_ _ ⟶ F.obj R) ≫
        (φ ≫ (Mod.regularLift (Mod.regular S) (scalarSection Λ X a)).hom)
    rw [← Category.assoc, Mod.one_comp_regularLift, ← Category.assoc,
      IsMonHom.one_hom φ, Mod.one_comp_regularLift]
    rfl
  have he := Mod.regularExtensionIso_naturality φ
    (Mod.regularLift (Mod.regular (F.obj R)) (Functor.LaxMonoidal.ε F ≫ F.map a))
    (Mod.regularLift (Mod.regular S) (scalarSection Λ X a)) (congrArg Mod.Hom.hom h)
  dsimp only [finiteConstantScalarExtension, scalarRegularIso, Functor.comp_map,
    Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← (Mod.extendScalars φ).map_comp, hm,
    (Mod.extendScalars φ).map_comp, Category.assoc, he]
  exact (Category.assoc _ _ _).symm

private instance scalarConstant_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (scalarConstant X) := by
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  unfold scalarConstant upperStarFromPoint
  infer_instance

private instance scalarExtension_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (finiteConstantScalarExtension Λ X) := by
  unfold finiteConstantScalarExtension
  infer_instance

private instance scalarExtension_additive (X : Scheme.{u}) :
    (finiteConstantScalarExtension Λ X).Additive := by
  have : PreservesBinaryBiproducts (finiteConstantScalarExtension Λ X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private noncomputable def scalarFreeIso (X : Scheme.{u}) (n : ℕ) :
    (finiteConstantScalarExtension Λ X).obj (Mod.finiteFree (scalarRingObj Λ) n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n :=
  (finiteConstantScalarExtension Λ X).mapBiproduct
      (fun _ : Fin n ↦ Mod.regular (scalarRingObj Λ)) ≪≫
    biproduct.mapIso (fun _ ↦ scalarRegularIso Λ X)

private theorem scalarMatrix_map (X : Scheme.{u}) {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    (scalarFreeIso Λ X m).inv ≫ (finiteConstantScalarExtension Λ X).map
        (biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular (scalarRingObj Λ))
          (A j k)) ≫ (scalarFreeIso Λ X n).hom = scalarMatrix Λ X A := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  simp only [scalarFreeIso, Iso.trans_inv, Iso.trans_hom, biproduct.mapIso_inv,
    biproduct.mapIso_hom, Category.assoc, biproduct.ι_map_assoc,
    Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
    biproduct.ι_desc_assoc, biproduct.map_π, biproduct.lift_π,
    scalarMatrix, biproduct.matrix]
  erw [biproduct.lift_π_assoc]
  simp only [← Category.assoc, ← Functor.map_comp, biproduct.ι_desc,
    biproduct.lift_π]
  simp only [Category.assoc]
  rw [scalarRegular_entry, Iso.inv_hom_id_assoc]

omit [IsCommMonObj Λ] in
private theorem scalarMatrix_reconstruct {m n : ℕ}
    (f : Mod.finiteFree (scalarRingObj Λ) m ⟶ Mod.finiteFree (scalarRingObj Λ) n) :
    (biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular (scalarRingObj Λ))
      ((MonObj.one : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) ≫
        (biproduct.ι _ j ≫ f ≫ biproduct.π _ k).hom)) = f := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  erw [biproduct.ι_matrix, biproduct.lift_π]
  apply Mod.regular_hom_ext
  simpa only [Category.assoc] using Mod.one_comp_regularLift (A := scalarRingObj Λ) _ _

/-- Finite constant local models on a specified pro-étale cover: the model on each
member is extension of a finitely presented scalar module, with no uniform rank bound.
Source: blueprint local-model definition, second paragraph and Lemma (1)
(blueprint: det-def-sfb-constructible-local-model). -/
def HasFiniteConstantLocalModelOnCover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) : Prop :=
  ∀ i : 𝒰.I₀, ∃ P : Mod Ab.{u + 1} (scalarRingObj Λ),
    Mod.IsFinitelyPresented (scalarRingObj Λ) P ∧
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj M ≅
        (finiteConstantScalarExtension Λ (𝒰.X i)).obj P)

/-- Scalar finite-presentation matrices on a specified pro-étale cover.
Source: blueprint local-model definition, Lemma (2)
(blueprint: det-def-sfb-constructible-local-model). -/
def HasScalarMatrixPresentationOnCover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) : Prop :=
  ∀ i : 𝒰.I₀, ∃ (m n : ℕ)
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)),
    Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj M ≅
      cokernel (scalarMatrix Λ (𝒰.X i) A))

private noncomputable def pointScalarSection
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ :=
  Functor.LaxMonoidal.ε (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a ≫
    (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app Λ

omit [MonObj Λ] [IsCommMonObj Λ] in
private theorem pointScalarSection_surjective :
    Function.Surjective (pointScalarSection Λ) := by
  intro b
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  refine ⟨adj.homEquiv _ _ (Functor.OplaxMonoidal.η F ≫ b), ?_⟩
  change Functor.LaxMonoidal.ε F ≫
    (F.map (adj.homEquiv _ _ _) ≫ adj.counit.app Λ) = b
  have h := (adj.homEquiv _ _).symm_apply_apply (Functor.OplaxMonoidal.η F ≫ b)
  rw [adj.homEquiv_counit] at h
  calc
    _ = Functor.LaxMonoidal.ε F ≫ (Functor.OplaxMonoidal.η F ≫ b) :=
      congrArg (fun f ↦ Functor.LaxMonoidal.ε F ≫ f) h
    _ = b := by rw [← Category.assoc, Functor.Monoidal.ε_η, Category.id_comp]

omit [MonObj Λ] [IsCommMonObj Λ] in
private theorem scalarSection_point (X : Scheme.{u})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    scalarSection Λ X a = Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map (pointScalarSection Λ a) := by
  simp only [scalarSection, scalarCoefficientHom, pointScalarSection,
    Functor.map_comp]
  rfl

private instance pointMod_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits ((upperStarFromPoint X).mapMod Λ) := by
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  infer_instance

private instance pointMod_additive (X : Scheme.{u}) :
    ((upperStarFromPoint X).mapMod Λ).Additive := by
  have : PreservesBinaryBiproducts ((upperStarFromPoint X).mapMod Λ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private noncomputable def pointRegularIso (X : Scheme.{u}) :
    ((upperStarFromPoint X).mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X) :=
  Mod.isoMk (Iso.refl _) (by simp)

private noncomputable def pointFreeIso (X : Scheme.{u}) (n : ℕ) :
    ((upperStarFromPoint X).mapMod Λ).obj (Mod.finiteFree Λ n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n :=
  ((upperStarFromPoint X).mapMod Λ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    biproduct.mapIso (fun _ ↦ pointRegularIso Λ X)

omit [IsCommMonObj Λ] in
private theorem pointRegular_entry (X : Scheme.{u})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    ((upperStarFromPoint X).mapMod Λ).map
        (Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ a)) ≫
      (pointRegularIso Λ X).hom =
    (pointRegularIso Λ X).hom ≫
      Mod.regularLift (Mod.regular (condensedRingObj Λ X)) (scalarSection Λ X a) := by
  apply Mod.regular_hom_ext
  change (MonObj.one : 𝟙_ _ ⟶ (upperStarFromPoint X).obj Λ) ≫
      ((upperStarFromPoint X).map
        (Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ a)).hom ≫ 𝟙 _) =
    (MonObj.one : 𝟙_ _ ⟶ (upperStarFromPoint X).obj Λ) ≫ (𝟙 _ ≫ _)
  simp only [Category.comp_id, Category.id_comp]
  rw [Mod.one_comp_regularLift, Functor.obj.η_def, Category.assoc,
    ← Functor.map_comp, Mod.one_comp_regularLift, scalarSection_point]

omit [IsCommMonObj Λ] in
private theorem pointMatrix_map (X : Scheme.{u}) {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    (pointFreeIso Λ X m).inv ≫ ((upperStarFromPoint X).mapMod Λ).map
        (biproduct.matrix fun j k ↦
          Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ (A j k))) ≫
      (pointFreeIso Λ X n).hom = scalarMatrix Λ X A := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  simp only [pointFreeIso, Iso.trans_inv, Iso.trans_hom, biproduct.mapIso_inv,
    biproduct.mapIso_hom, Category.assoc, biproduct.ι_map_assoc,
    Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
    biproduct.ι_desc_assoc, biproduct.map_π, biproduct.lift_π,
    scalarMatrix, biproduct.matrix]
  erw [biproduct.lift_π_assoc]
  simp only [← Category.assoc, ← Functor.map_comp, biproduct.ι_desc,
    biproduct.lift_π]
  simp only [Category.assoc]
  rw [pointRegular_entry, Iso.inv_hom_id_assoc]

omit [IsCommMonObj Λ] in
private theorem pointMatrix_reconstruct {m n : ℕ}
    (f : Mod.finiteFree Λ m ⟶ Mod.finiteFree Λ n) :
    (biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular Λ)
      ((MonObj.one : 𝟙_ _ ⟶ Λ) ≫
        (biproduct.ι _ j ≫ f ≫ biproduct.π _ k).hom)) = f := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  erw [biproduct.ι_matrix, biproduct.lift_π]
  apply Mod.regular_hom_ext
  simpa only [Category.assoc] using Mod.one_comp_regularLift (A := Λ) _ _

/-- Constant finite scalar models and finite scalar matrices are equivalent on the
same given cover. Source: blueprint local-model lemma, and proof, Steps 1–3.
Proof: the constant-sheaf adjunction and extension/restriction adjunction identify maps
from E_U(P) to N with scalar-linear maps P → N(U). For P = R^k this identifies E_U(P)
with Λ_U^k, preserving each scalar matrix entry. For a scalar matrix A, maps from
E_U(coker A) to N are exactly maps from Λ_U^n killing A, so E_U(coker A) is its cokernel;
no flatness is used. Apply a finite presentation of each P_i for the forward direction.
Conversely take P_i to be the cokernel of the given scalar matrix over R.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem finiteConstantLocalModelOnCover_iff_scalarMatrix {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) :
    HasFiniteConstantLocalModelOnCover Λ M 𝒰 ↔
      HasScalarMatrixPresentationOnCover Λ M 𝒰 := by
  constructor
  · intro h i
    obtain ⟨P, ⟨n, m, f, ⟨ef⟩⟩, ⟨eP⟩⟩ := h i
    let A (j : Fin m) (k : Fin n) : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ :=
      (MonObj.one : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) ≫
        (biproduct.ι _ j ≫ f ≫ biproduct.π _ k).hom
    let E := finiteConstantScalarExtension Λ (𝒰.X i)
    have he : (scalarFreeIso Λ (𝒰.X i) m).inv ≫ E.map f ≫
        (scalarFreeIso Λ (𝒰.X i) n).hom = scalarMatrix Λ (𝒰.X i) A := by
      rw [← scalarMatrix_map, scalarMatrix_reconstruct]
    refine ⟨m, n, A, ⟨eP ≪≫ E.mapIso ef ≪≫ PreservesCokernel.iso E f ≪≫ ?_⟩⟩
    exact cokernel.mapIso (E.map f) (scalarMatrix Λ (𝒰.X i) A)
      (scalarFreeIso Λ (𝒰.X i) m) (scalarFreeIso Λ (𝒰.X i) n)
      (by rw [← he]; simp)
  · intro h i
    obtain ⟨m, n, A, ⟨e⟩⟩ := h i
    let f : Mod.finiteFree (scalarRingObj Λ) m ⟶ Mod.finiteFree (scalarRingObj Λ) n :=
      biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j k)
    let E := finiteConstantScalarExtension Λ (𝒰.X i)
    refine ⟨cokernel f, ⟨n, m, f, ⟨Iso.refl _⟩⟩, ⟨e ≪≫ ?_⟩⟩
    refine (cokernel.mapIso (E.map f) (scalarMatrix Λ (𝒰.X i) A)
      (scalarFreeIso Λ (𝒰.X i) m) (scalarFreeIso Λ (𝒰.X i) n) ?_).symm ≪≫
        (PreservesCokernel.iso E f).symm
    rw [← scalarMatrix_map]
    simp only [f, E, Iso.hom_inv_id_assoc]

/-- The existing finite constant local model predicate is exactly the scalar-extension
formulation. Source: blueprint local-model definition and proof, Steps 1–3.
Proof: a finite presentation by regular condensed modules is a finite scalar matrix,
since maps from the regular module are maps from the integer unit, hence sections
at the terminal profinite set. Its cokernel is extension of the corresponding
finitely presented scalar module by the adjunction and cokernel calculation of
Steps 1–3. Conversely present a scalar module by a finite matrix and take the
same matrix of regular condensed modules before inverse image. Inverse image and
extension of scalars preserve these cokernels. The same cover and its members
are used in both directions.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem finiteConstantLocalModel_iff_exists_cover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    HasFiniteConstantLocalModel Λ X M ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
        HasFiniteConstantLocalModelOnCover Λ M 𝒰 := by
  classical
  constructor
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, (finiteConstantLocalModelOnCover_iff_scalarMatrix Λ M 𝒰).mpr ?_⟩
    intro i
    obtain ⟨P, ⟨n, m, f, ⟨ef⟩⟩, ⟨eP⟩⟩ := h𝒰 i
    let b (j : Fin m) (k : Fin n) : 𝟙_ _ ⟶ Λ :=
      (MonObj.one : 𝟙_ _ ⟶ Λ) ≫ (biproduct.ι _ j ≫ f ≫ biproduct.π _ k).hom
    choose A hA using fun j k ↦ pointScalarSection_surjective Λ (b j k)
    let F := (upperStarFromPoint (𝒰.X i)).mapMod Λ
    have hf : (biproduct.matrix fun j k ↦
        Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ (A j k))) = f := by
      simp_rw [hA]
      exact pointMatrix_reconstruct Λ f
    have he : (pointFreeIso Λ (𝒰.X i) m).inv ≫ F.map f ≫
        (pointFreeIso Λ (𝒰.X i) n).hom = scalarMatrix Λ (𝒰.X i) A := by
      rw [← pointMatrix_map, hf]
    refine ⟨m, n, A, ⟨eP ≪≫ F.mapIso ef ≪≫ PreservesCokernel.iso F f ≪≫ ?_⟩⟩
    exact cokernel.mapIso (F.map f) (scalarMatrix Λ (𝒰.X i) A)
      (pointFreeIso Λ (𝒰.X i) m) (pointFreeIso Λ (𝒰.X i) n)
      (by rw [← he]; simp)
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨m, n, A, ⟨e⟩⟩ :=
      (finiteConstantLocalModelOnCover_iff_scalarMatrix Λ M 𝒰).mp h𝒰 i
    let f : Mod.finiteFree Λ m ⟶ Mod.finiteFree Λ n :=
      biproduct.matrix fun j k ↦
        Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ (A j k))
    let F := (upperStarFromPoint (𝒰.X i)).mapMod Λ
    refine ⟨cokernel f, ⟨n, m, f, ⟨Iso.refl _⟩⟩, ⟨e ≪≫ ?_⟩⟩
    refine (cokernel.mapIso (F.map f) (scalarMatrix Λ (𝒰.X i) A)
      (pointFreeIso Λ (𝒰.X i) m) (pointFreeIso Λ (𝒰.X i) n) ?_).symm ≪≫
        (PreservesCokernel.iso F f).symm
    rw [← pointMatrix_map]
    simp only [f, F, Iso.hom_inv_id_assoc]

private theorem map_finitePresentation
    {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    (R : C) (S : D) [MonObj R] [MonObj S]
    [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]
    (F : Mod C R ⥤ Mod D S) [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    (M : Mod C R) (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S (F.obj M) := by
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := F.additive_of_preservesBinaryBiproducts
  obtain ⟨n, m, f, ⟨h⟩⟩ := hM
  let b (k : ℕ) : F.obj (Mod.finiteFree R k) ≅ Mod.finiteFree S k :=
    F.mapBiproduct (fun _ : Fin k ↦ Mod.regular R) ≪≫
      biproduct.mapIso (fun _ ↦ e)
  let g := (b m).inv ≫ F.map f ≫ (b n).hom
  refine ⟨n, m, g, ⟨F.mapIso h ≪≫ PreservesCokernel.iso F f ≪≫ ?_⟩⟩
  exact cokernel.mapIso (F.map f) g (b m) (b n) (by simp [g])

/-- Finite constant local models imply local finite presentation.
Source: blueprint local-model final paragraph and proof, Step 4.
Proof: replace each constant scalar model by its scalar matrix presentation using
finiteConstantLocalModelOnCover_iff_scalarMatrix. This is a finite free presentation
over Λ_U. Transport along the canonical coefficient isomorphism α_u to the
u^*Λ_X-module category used by IsLocallyFinitelyPresented. Restriction along α_u and
its inverse preserve regular modules, finite sums and cokernel presentations, so the
same cover witnesses local finite presentation.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem HasFiniteConstantLocalModel.isLocallyFinitelyPresented {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := h𝒰 i
  let F := (upperStarFromPoint (𝒰.X i)).mapMod Λ
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (upperStarFromPoint (𝒰.X i)) := by
    unfold upperStarFromPoint
    infer_instance
  have : PreservesFiniteColimits F := by
    dsimp only [F]
    infer_instance
  have hF : Mod.IsFinitelyPresented (condensedRingObj Λ (𝒰.X i)) (F.obj P) :=
    map_finitePresentation Λ _ F (Mod.isoMk (Iso.refl _) (by simp)) P hP
  let φ := condensedPullbackHom Λ (𝒰.f i)
  let E := Mod.comapEquivalenceOfIsIso φ
  have : (Mod.comap φ).IsEquivalence := E.isEquivalence_functor
  let er : (Mod.comap φ).obj (Mod.regular (condensedRingObj Λ (𝒰.X i))) ≅
      Mod.regular ((upperStar Ab.{u + 1} (𝒰.f i)).obj (condensedRingObj Λ X)) := by
    exact (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  have hG := map_finitePresentation _ _ (Mod.comap φ) er (F.obj P) hF
  obtain ⟨n, m, f, ⟨hf⟩⟩ := hG
  refine ⟨n, m, f, ⟨?_ ≪≫ hf⟩⟩
  let N := ((upperStar Ab.{u + 1} (𝒰.f i)).mapMod (condensedRingObj Λ X)).obj M
  exact ((Mod.comapId _).app N).symm ≪≫
    (Mod.comapCongr (IsIso.hom_inv_id φ).symm).app N ≪≫
    (Mod.comapComp φ (inv φ)).app N ≪≫
    (Mod.comap φ).mapIso ((Mod.extendScalarsIsoComapInv φ).app N).symm ≪≫
    (Mod.comap φ).mapIso e

attribute [local irreducible] CondensedRing.upperStar finiteConstantScalarExtension

private theorem scalarSections_monoidal_eq :
    scalarSections_laxMonoidal.{u} =
      sectionsMonoidal (A := Ab.{u + 1}) (coherentTopology Profinite.{u})
        (T := Profinite.of PUnit.{u + 1}) := by
  let := sectionsMonoidal (A := Ab.{u + 1}) (coherentTopology Profinite.{u})
    (T := Profinite.of PUnit.{u + 1})
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  have : adj.IsMonoidal := inferInstance
  apply Functor.LaxMonoidal.ext
  · exact (Adjunction.IsMonoidal.leftAdjoint_ε (adj := adj)).symm
  · funext X Y
    exact (Adjunction.IsMonoidal.leftAdjoint_μ (adj := adj) X Y).symm

private noncomputable def internalRegularCoordinates (K : Type*) [Ring K] :
    (internalToModule K).obj (Mod.regular (AddCommGrpCat.of K)) ≃ₗ[K] K where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end AlgebraicGeometry.ProEtale
