/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleExternalKunneth
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothBaseChangeCoefficients
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersionBaseChange
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Pasting
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.CategoryTheory.ExactDeltaEmbeddingDetection
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.CategoryTheory.Sites.LocalSite
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsSerre
import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsPullback
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.Flat.FlatModel

/-! # The field-coefficient step of identity-factor external Künneth

Source: current blueprint, sk-lem-sf-kunneth-star, Field coefficients and sheaves,
and Complexes over L (blueprint: lem-sf-external-kunneth-finite-field).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale
variable (L : Type (u + 1)) [Field L] [Finite L]

/-- Identity-factor Künneth with finite field coefficients.
Source: sk-lem-sf-kunneth-star, Field coefficients and sheaves and Complexes over L
(blueprint: lem-sf-external-kunneth-finite-field).

Proof: First take both inputs to be constructible sheaves. Independent base change
for the constant coefficient unit gives the constant second-factor case. The
finite-cover tensor-counit comparison identifies the map on finite direct images
of constants with a finite pushforward of this exchange; its explicit counit
identity is needed, rather than an abstract isomorphism of endpoints. It also
handles finite direct sums. Embed each constructible second sheaf into such a
sum, with constructible quotient. The source cohomology functors are exact since
L is a field, and the target cohomology functors form a cohomological delta functor.
Apply exactDeltaComparison_isIso_of_embeddings to the natural homology maps.
Negative cohomology vanishes for sheaf inputs. The derived homology criterion
makes the map invertible. Both functors and the comparison respect shifts and
triangles; finite truncation triangles in each variable extend the result to
bounded constructible complexes. Over L the cohomology sheaves are flat, so the
truncations have finite Tor amplitude. Constructible/direct-image comparison,
monoidal pullback, and the ordinary/internal-module equivalence transport this
specified counit adjunct between the étale and pro-étale presentations. -/
theorem isIso_externalKunnethIdentityMap_finiteField
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (_hp : (ringChar k).Prime) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar k)
    (_hA : ∃ n : ℕ, 0 < n ∧ ((l ^ n : ℕ) : L) = 0)
    {X Y T : Scheme.{u}} (b : Y ⟶ Spec (.of k)) (c : T ⟶ Spec (.of k))
    (f : X ⟶ Y)
    [LocallyOfFiniteType b] [QuasiCompact b] [IsSeparated b]
    [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
    [LocallyOfFiniteType (f ≫ b)] [QuasiCompact (f ≫ b)] [IsSeparated (f ≫ b)]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} L)))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} L)))
    (_hM : exceptionalTransportProEtaleObjects L X M)
    (_hQ : exceptionalTransportProEtaleObjects L T Q) :
    IsIso (externalKunnethIdentityMap L
      ⟨(pullback.mapOverBaseRight_fst f b c).symm⟩
      (pullback.mapOverBaseRight_snd f b c) M Q) := by
  sorry

end AlgebraicGeometry.ProEtale
