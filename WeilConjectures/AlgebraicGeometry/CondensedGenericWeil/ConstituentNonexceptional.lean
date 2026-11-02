/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.RealCondensedFibre.RealCondensedFibreFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.MonCat.FilteredColimits
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.ConstructibleSheaf.Pullback
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralFibrePathConstruction
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.ConstructibleSheaf.Biproduct
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.AlgebraicGeometry.GaloisPointGeometricComparison
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Rational.RationalFibrePathConstruction
public import Mathlib.CategoryTheory.Localization.Construction
public import WeilConjectures.AlgebraicGeometry.Rational.RationalFibrePathScalarSquare
public import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientFiberComparisons
public import WeilConjectures.CategoryTheory.Pseudofunctor.NormalizedFibreComparisons
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
public import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier

/-! # Constituent-nonexceptionality on the condensed Weil model

This is the current condensed-coefficient formulation of the affine-line definition in the
latest blueprint.  A geometric constituent is represented by a lisse condensed Weil
subobject followed by an epimorphism to the indicated linear Artin--Schreier module.

Source: `literature/blueprint/latest/blueprint/`
`sec-deligne-laumon-a1/sk-p-dl-a1-middle/def-a1-constituent-nonexceptional.md`,
node `def-a1-constituent-nonexceptional`, both definition paragraphs
(blueprint: `def-a1-constituent-nonexceptional`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
variable (ell : ℕ) [Fact ell.Prime]
variable (j₀ : U₀ ⟶ Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀)))

local instance affineLineModel_locallyOfFiniteType :
    LocallyOfFiniteType (Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (affineLine D.k₀ ↘ Spec (.of D.k₀)))
local instance affineLineModel_quasiCompact :
    QuasiCompact (Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))).hom :=
  inferInstanceAs (QuasiCompact (affineLine D.k₀ ↘ Spec (.of D.k₀)))

local instance geometricFiber_over :
    (D.geometricFiber U₀).left.Over (Spec (.of D.k)) :=
  ⟨(D.geometricFiber U₀).hom⟩
local instance geometricFiber_over_base :
    (D.geometricFiber U₀).left.Over (Spec (.of D.k₀)) :=
  ⟨(D.geometricFiber U₀).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))⟩

/-- The affine-line coordinate on the geometric open, pulled back along `j₀`.

Source: `literature/blueprint/latest/blueprint/`
`sec-deligne-laumon-a1/sk-p-dl-a1-middle/def-a1-constituent-nonexceptional.md`,
the geometric-coefficient pullback clause
(blueprint: `def-a1-constituent-nonexceptional`). -/
noncomputable def geometricCoordinate
    (j₀ : U₀ ⟶ Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))) :
    Γ((D.geometricFiber U₀).left, ⊤) :=
  (pullback.fst U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).appTop
    (j₀.left.appTop (AffineSpace.coord (Spec (.of D.k₀)) PUnit.unit))

/-- The condensed linear Artin--Schreier module with parameter `a`, on the geometric open.

Source: `literature/blueprint/latest/blueprint/`
`sec-deligne-laumon-a1/sk-p-dl-a1-middle/def-a1-constituent-nonexceptional.md`,
the Artin--Schreier restriction clause
(blueprint: `def-a1-constituent-nonexceptional`). -/
noncomputable def linearArtinSchreierModule
    (j₀ : U₀ ⟶ Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀)))
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell)))
    (a : D.k) : RealCondensedFibre.Modules
      (Profinite.padicAlgClRingObj ell) (D.geometricFiber U₀).left :=
  letI := Fintype.ofFinite D.k₀
  condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ell) D.k₀
    (D.geometricFiber U₀).left ψ
    (((D.geometricFiber U₀).hom.appTop
      ((Scheme.ΓSpecIso (.of D.k)).inv.hom a)) * geometricCoordinate D U₀ j₀)

/-- A geometric Jordan--Hölder constituent of `F` is presented by a lisse condensed
subobject and an epimorphism onto the corresponding linear Artin--Schreier module.

Source: `literature/blueprint/latest/blueprint/`
`sec-deligne-laumon-a1/sk-p-dl-a1-middle/def-a1-constituent-nonexceptional.md`,
the geometric irreducible constituent paragraph
(blueprint: `def-a1-constituent-nonexceptional`). -/
def HasLinearCondensedArtinSchreierConstituent
    (j₀ : U₀ ⟶ Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀)))
    (F : Lisse ell (D.geometricFrobenius U₀))
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell)))
    (a : D.k) : Prop :=
  ∃ (B : Lisse ell (D.geometricFrobenius U₀))
    (i : B.obj.carrier ⟶ F.obj.carrier)
    (q : B.obj.carrier ⟶ linearArtinSchreierModule D U₀ ell j₀ ψ a),
    Mono i ∧ Epi q

/-- Constituent-nonexceptionality excludes every linear Artin--Schreier constituent,
including the parameter `a = 0`.

Source: `literature/blueprint/latest/blueprint/`
`sec-deligne-laumon-a1/sk-p-dl-a1-middle/def-a1-constituent-nonexceptional.md`,
both definition paragraphs
(blueprint: `def-a1-constituent-nonexceptional`). -/
def IsConstituentNonexceptional
    (F : Lisse ell (D.geometricFrobenius U₀))
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell))) : Prop :=
  ∀ a : D.k, ¬ HasLinearCondensedArtinSchreierConstituent D U₀ ell j₀ F ψ a


end AlgebraicGeometry.ProEtale.CondensedGenericWeil
