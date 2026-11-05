/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleExchange
public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
public import Mathlib.CategoryTheory.Preadditive.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.CategoryTheory.Triangulated.RecollementTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.TraceFormula.OpenCover
public import WeilConjectures.TraceFormula.PointTrace
public import WeilConjectures.TraceFormula.PointComplement
public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftRetraction
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsAb
public import WeilConjectures.TraceFormula.Specialization.Trait
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedLiftSections
public import WeilConjectures.CategoryTheory.Adjunction.MatePasting
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndDerived
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionDerived
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.RingTheory.TensorProduct.Finite
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import Mathlib.Algebra.Module.Presentation.Finite
public import Mathlib.Algebra.Module.Presentation.Tensor
public import Mathlib.Init
public import Lean.Elab.Tactic.ElabTerm
public import WeilConjectures.CategoryTheory.DerivedCategory.ProductsMapDerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin
public import Mathlib.RingTheory.PowerSeries.Ideal
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity
public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
public import WeilConjectures.TraceFormula.Specialization.TraitSlice
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicIntegers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginReadingProof
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationUniversal
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisCoverTrace
public import WeilConjectures.CategoryTheory.Adjunction.ConjugateCounit
public import WeilConjectures.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing
public import WeilConjectures.SixFunctors.ProEtale.GaloisActionSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.BaseChange
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGerm
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import WeilConjectures.RingTheory.HenselianDVRExtension
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
public import WeilConjectures.RingTheory.CompletionOfDVR
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.GroupTheory.IndexNormal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.DerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonUnit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import Mathlib.Tactic.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTransition
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTransitionComplex
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterComplete
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleRetract
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
public import WeilConjectures.ConstructibleSheaf.SpecializationCriterion
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtensionIso
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProperNoetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegralCriterion
public import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit

/-!

# The dualizing maps of nearby cycles over the trait

Let `S = Spec k'⟦t⟧` be the strictly henselian trait, `k'` separably closed. A model `M` of a
separated `k`-scheme `X` of finite type is a *trait model of `X` over the base*
(`NearbyCyclesModel.IsTraitModelOfBase`) if it is of finite type over `S` along `q : 𝒳 ⟶ S`,
its identification `ε : 𝒳_Ω ⟶ X` factors through a `k`-morphism `𝒳 ⟶ X` (`𝒳` being a `k`-scheme
through `q` and `S ⟶ Spec k`), and its geometric generic fibre
is the base change `X ×_k Spec Ω`. Such a model maps to the trait model of the point
(`ProEtale.CondensedRing.traitModel`) over the structure morphisms
(`NearbyCyclesModel.IsTraitModelOfBase.toTrait`), with proper exchange
`χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_X` (`NearbyCyclesModel.IsTraitModelOfBase.pushforwardExchange`).

The *dualizing map* `θ_X : Ψ_X ω_X ⟶ ω_{X'}` (blueprint `det-nearby-exchange-maps` (5),
`θ_X = β_{a_X}(A)`) is the exceptional adjoint of the compact-support exchange `ν_{a_X}`, read
through the specialization unit of the trait and the base change `Lε^* ω_{X/k} ≅ ω_{𝒳_Ω/Ω}`.
The compact-support exchange is built from a relative compactification of `𝒳` over `S`, and is
independent of the choice (`NearbyCyclesModel.IsTraitModelOfBase.dualizingMap`, downstream).
A family of maps `θ` with the two properties
that characterize the dualizing maps is a `NearbyCyclesModel.NearbyDualizingData`, and its
existence is the node lemma `NearbyCyclesModel.nonempty_nearbyDualizingData` (blueprint
`det-nearby-exchange-maps` and the composition law `sk-lem-tf-nearby-mate-coherences` (4)):

* **proper models**: for `q` proper and geometric generic fibre all of `X ×_k Spec Ω`,
  `ν_{a} = χ_a⁻¹` under `Ra_! ≅ Ra_*`, so `θ_X` is the unique
  map with `tr_{X'} ∘ Ra'_*(θ_X) ∘ χ_a(ω_X) = σ⁻¹ ∘ Ψ_S(tr_X)`, `tr` the traces
  `Ra_* ω_X ≅ Ra_! Ra^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` (`NearbyCyclesModel.trace`) and `σ` the specialization unit
  of the trait;
* **open restriction**: for an open sub-model `N ⊆ M` over open immersions `j`, `j'`,
  `θ_N = j'^* θ_M ∘ β_j(ω_X)` with `β_j = α_j⁻¹` and `j^! = j^*`, that is
  `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)` for the identifications `ρ : j^* ω_X ≅ ω_Y`.

These two properties determine the family `θ`: every trait model is an open sub-model of a proper
one whose geometric generic fibre is all of `X̄ ×_k Spec Ω`
(`NearbyCyclesModel.IsTraitModelOfBase.exists_isProper_openSubmodel`), the proper exchange `χ_a`
is then invertible, and maps
`A ⟶ ω_{X'}` are determined by their traces.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (k : Type u) [Field k] {k' : Type u} [Field k'] [Algebra k k']

variable {k} {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

namespace IsTraitModelOfBase

end IsTraitModelOfBase

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- The trace `tr_X : Ra_* ω_X ≅ Ra_! Ra^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` of a proper `k`-scheme: the counit of
`Ra_! ⊣ Ra^!` read through `Ra_! ≅ Ra_*`. -/
noncomputable def trace (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsProper (toPoint Z).left] :
    (boundedConstructibleLowerStar ℓ (toPoint Z)).obj
        (dualizingComplex ℓ Z) ⟶ 𝟙_ _ :=
  (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z)).inv.app _ ≫
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z)).counit.app (𝟙_ _)

variable (k k')

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
