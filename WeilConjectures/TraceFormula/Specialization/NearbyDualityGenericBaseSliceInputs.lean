/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityMap
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap
public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethProper
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
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModLimits
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsAb
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperStarMapModLimits
public import WeilConjectures.TraceFormula.OpenCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin
public import Mathlib.RingTheory.PowerSeries.Ideal
public import WeilConjectures.TraceFormula.Specialization.Trait
public import WeilConjectures.TraceFormula.Specialization.TraitProduct
public import WeilConjectures.AlgebraicGeometry.ClosedPointsFiberProduct
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.CategoryTheory.Triangulated.RecollementTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented
public import WeilConjectures.TraceFormula.PointTrace
public import WeilConjectures.TraceFormula.PointComplement
public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.Specialization.TraitSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel
public import WeilConjectures.TraceFormula.Specialization.TraitModelCompactification
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftRetraction
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedLiftSections
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
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

/-!

# Nearby duality over a generic base: the inputs of the slice step

Let `M` be a trait model of `X₁` over the generic base, `b : 𝒳 ⟶ 𝔸¹_S` a coordinate of its total
space and `M''` the generic slice model of `b` (`NearbyCyclesModel.genericSliceModel`), a trait
model over the generic base `(Frac K⟦t⟧, X₂)`, with special fibre `Y = 𝒳''_s`. This file sets up
the proof of the slice compatibility of nearby duality
(`NearbyCyclesModel.isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase`, blueprint
`det-tf-nearby-duality-slice` (2) with `det-tf-invariants-duality`):

* the pullback `Lg^*` of bounded constructible complexes along a morphism of schemes of finite
  type over possibly different fields (`boundedConstructibleUpperStarOfMap`), strong monoidal;
* the morphism of models `M'' ⟶ M` over `c : X₂ ⟶ X₁` and `p : Y ⟶ X'`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceHom`) and its pullback exchange
  `α : p^* Ψ_M ⟶ Ψ_{M''} c^*` (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchange`),
  which is monoidal (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchange_tensor`);
* the action of the self-maps of a model over the identities on its nearby cycles
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceSelfAction`), which is monoidal
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceSelfAction_tensor`);
* the duality map of the slice for the dualizing objects `c^* ω_{X₁}` and `p^* ω_{X'}`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceDualityMap`).

The other inputs of the slice step are in separate files: the averaging splitting of `α`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_averaging_genericSliceExchange`, in
`WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceAveraging`), the
commutation of the pullbacks with internal Hom (blueprint `det-pd-generic-closed-hom` (2), in
`WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceClosedHom`) and the
dualizing map of the slice
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_genericSliceDualizingMap`, in
`WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceDualizing`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

section UpperStarOfMap

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)] {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The derived pullback `Lg^* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible complexes
along a morphism of schemes `g : Y ⟶ X`, `X` and `Y` of finite type over possibly different
fields: the restriction of `L((g)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable def boundedConstructibleUpperStarOfMap (g : Y.left ⟶ X.left) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g K.obj K.property

/-- The derived pullback along a morphism of schemes is strong monoidal on bounded constructible
complexes, with the comparison isomorphisms of `L((g)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStarOfMap (g : Y.left ⟶ X.left) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g).Monoidal := by
  unfold boundedConstructibleUpperStarOfMap
  exact ObjectProperty.monoidalLift _ _

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The derived pullback along a morphism of schemes on bounded constructible complexes is that
of the ambient derived categories. -/
lemma boundedConstructibleUpperStarOfMap_map (g : Y.left ⟶ X.left)
    {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : A ⟶ B) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g).map f =
      ObjectProperty.homMk (L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map f.hom) :=
  rfl

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₂).Prime] [IsSeparated X.hom]
  [IsSeparated Y.hom] in
/-- The tensor comparison of the derived pullback along a morphism of schemes on bounded
constructible complexes is that of the ambient derived pullback. -/
lemma μ_boundedConstructibleUpperStarOfMap (g : Y.left ⟶ X.left)
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g) A B =
      ObjectProperty.homMk
        (Functor.LaxMonoidal.μ L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧) A.obj B.obj) :=
  rfl

end UpperStarOfMap

namespace NearbyCyclesModel

section LiftExchange

variable {ℓ : ℕ} [Fact ℓ.Prime] {k₁ k₁' k₂ k₂' : Type u} [Field k₁] [Field k₁'] [Field k₂]
  [Field k₂'] [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₁').Prime]
  [Fact (ringChar k₁' ≠ ℓ)] [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  [Fact (ringChar k₂').Prime] [Fact (ringChar k₂' ≠ ℓ)]
  {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k₁'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {Y' : Over (Spec (.of k₂'))}
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {j : Y.left ⟶ X.left} {j' : Y'.left ⟶ X'.left}

end LiftExchange

/-! ### The generic slice -/

section GenericSlice

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {K : Type u} [Field K] [Algebra k' K] (x : K)

section Hom

end Hom

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [IsSepClosed K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries K))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries K)) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase x hb).hom] [QuasiCompact (genericSliceBase x hb).hom]
  [IsSeparated (genericSliceBase x hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice x)).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice x)).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice x)).hom]

namespace IsTraitModelOfGenericBase

end IsTraitModelOfGenericBase

end GenericSlice

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
