/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
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
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity
public import WeilConjectures.TraceFormula.Specialization.Trait
public import WeilConjectures.AlgebraicGeometry.ClosedPointsFiberProduct
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.CategoryTheory.Triangulated.RecollementTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented
public import WeilConjectures.TraceFormula.PointTrace
public import WeilConjectures.TraceFormula.PointComplement
public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# Generic slices of trait models of the base

Let `M` be a trait model over the base of a `k`-scheme `X` (`NearbyCyclesModel.IsTraitModelOfBase`),
with total space `𝒳` over the trait `S = Spec k'⟦t⟧`, and let `e : 𝒳 ⟶ X` be the factorisation of
its identification `ε`. Let `b₀ : X ⟶ 𝔸¹_k` be a coordinate on `X` and `b : 𝒳 ⟶ 𝔸¹_S` a
coordinate on `𝒳` over `S` lifting `e ≫ b₀`. Let `K` be a field extension of `k'` and of the
rational function field `k(x) = RatFunc k` (compatibly over `k`), and let the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`AlgebraicGeometry.traitSlice`) be taken at the image of `x` in `K`.
The base change of `M` along `σ` (`NearbyCyclesModel.baseChange`) is then a trait model over the
base of the generic fibre `X₁ = X ×_{𝔸¹_k} Spec k(x)` of `b₀`
(`AlgebraicGeometry.genericCoordinateFibre`), as a `k(x)`-scheme, with trait field `K`:
this is `NearbyCyclesModel.isTraitModelOfBase_sliceBaseModel`.

The geometric generic fibre `𝒳'' ×_{K⟦t⟧} Spec Ω_K` of the slice is
`𝒳_η̄ ×_{𝔸¹_Ω} Spec Ω_K`, and the open immersion `𝒳_η̄ ⟶ X ×_k Spec Ω` base changes to an open
immersion into `(X ×_k Spec Ω) ×_{𝔸¹_Ω} Spec Ω_K = X ×_{𝔸¹_k} Spec Ω_K = X₁ ×_{k(x)} Spec Ω_K`.

For `K = k'(x)^alg` (`AlgebraicGeometry.traitSliceField`) and `x ↦ traitSliceCoord k'`, the
embedding `k(x) ⟶ K` is `AlgebraicGeometry.sliceBaseRingHom`
(`NearbyCyclesModel.isTraitModelOfBase_sliceBaseModel_traitSliceField`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section SliceBaseField

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

end SliceBaseField

section SlicePoint

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k'] {K : Type u} [Field K]
  [Algebra k' K] [Algebra (RatFunc k) K] {x : K}

end SlicePoint

section CoordinateBaseChange

variable {n : Type u} {S X T : Scheme.{u}} (b₀ : X ⟶ 𝔸(n; S)) {p : X ⟶ S}
  (hb₀ : b₀ ≫ 𝔸(n; S) ↘ S = p) (f : T ⟶ S)

/-- The base change `X ×_S T ⟶ 𝔸ⁿ_T` of a coordinate `b₀ : X ⟶ 𝔸ⁿ_S` over `S`. -/
noncomputable def coordinateBaseChange : pullback p f ⟶ 𝔸(n; T) :=
  (AffineSpace.isPullback_map f).lift (pullback.fst _ _ ≫ b₀) (pullback.snd _ _) (by
    rw [Category.assoc, hb₀, pullback.condition])

@[reassoc (attr := simp)]
lemma coordinateBaseChange_map :
    coordinateBaseChange b₀ hb₀ f ≫ AffineSpace.map n f = pullback.fst _ _ ≫ b₀ :=
  (AffineSpace.isPullback_map f).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma coordinateBaseChange_over :
    coordinateBaseChange b₀ hb₀ f ≫ 𝔸(n; T) ↘ T = pullback.snd _ _ :=
  (AffineSpace.isPullback_map f).lift_snd _ _ _

/-- The base change of a coordinate is a base change: `X ×_S T = X ×_{𝔸ⁿ_S} 𝔸ⁿ_T`. -/
lemma isPullback_coordinateBaseChange :
    IsPullback (pullback.fst p f) (coordinateBaseChange b₀ hb₀ f) b₀ (AffineSpace.map n f) :=
  IsPullback.of_bot (by rw [coordinateBaseChange_over, hb₀]; exact IsPullback.of_hasPullback p f)
    (coordinateBaseChange_map b₀ hb₀ f).symm (AffineSpace.isPullback_map f)

end CoordinateBaseChange

section GenericCoordinateFibre

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}

end GenericCoordinateFibre

namespace ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k'] {K : Type u} [Field K]
  [Algebra k' K] [Algebra (RatFunc k) K] {x : K}
  (hX : algebraMap (RatFunc k) K RatFunc.X = x)
  (hC : (algebraMap (RatFunc k) K).comp (algebraMap k (RatFunc k)) =
    (algebraMap k' K).comp (algebraMap k k'))
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  (b₀ : X.left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  {e : M.total ⟶ X.left}
  (hbe : b ≫ AffineSpace.map (ULift.{u} (Fin 1)) (traitToBase k k') = e ≫ b₀)

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
