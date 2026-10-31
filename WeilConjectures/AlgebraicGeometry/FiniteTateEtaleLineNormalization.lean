/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.FiniteTateSiteDescentDefinitions

/-! # Degree-one finite Tate line normalization

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/
sk-lem-geo-cartier.proof.md, pullback paragraph (blueprint:
lem-amb-finite-tate-etale-line-normalization).

## Main statement

* `ordinaryFiniteLineNormalization_finiteTateEtalePullback`: the normalized
  degree-one line comparison satisfies the finite Tate pullback predicate.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Etale AlgebraicGeometry.Scheme
open scoped ChangeOfRings

namespace AlgebraicGeometry.Etale

/--
The line normalization of an ordinary finite Tate transport is exactly the
finite Tate etale pullback predicate in degree one.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md, pullback paragraph
(blueprint: lem-amb-finite-tate-etale-line-normalization).

Proof: put `N = l ^ (r + 1)` and obtain its invertibility on `T` from the
invertibility of `l`.  Unfold the degree-one finite Tate pullback predicate.
The roots normalization of `t` identifies the root over the base change with
the transported root: transpose the normalization across the inverse-image
adjunction, evaluate it on the root section, and use injectivity of the kernel
inclusion into the units.  The degree-one line normalization of `t` then sends
the one-generator to the one-generator for that transported root, which is
exactly the required predicate equation.  This argument does not assert an
existence or flatness property.
-/
theorem ordinaryFiniteLineNormalization_finiteTateEtalePullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (t : OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hA)
    {T' T : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (l : Γ(T, ⊤))) :
    Scheme.IsFiniteTateEtalePullback l E n T v r hA 1
      (t.line v (by simpa only [Nat.cast_pow] using hT.pow (r + 1))) := by
  let H : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (r + 1)
  intro U a z z' hz
  have hroot :
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
        (t.roots v H).hom).hom.app U (z 0) = z' 0 := by
    have h := congrArg
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _)
      (t.roots_normalization v H)
    rw [Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right] at h
    unfold upperStarGmSheafToGmSheaf at h
    rw [Equiv.apply_symm_apply] at h
    have hv := congrArg (fun f ↦ Additive.toMul ((f.hom.app U (z 0)).down)) h.symm
    have hinj : Mono (kernel.ι ((l ^ (r + 1)) • 𝟙 T'.gmSheaf)).hom :=
      (sheafToPresheaf _ _).map_mono _
    apply (AddCommGrpCat.mono_iff_injective
      ((kernel.ι ((l ^ (r + 1)) • 𝟙 T'.gmSheaf)).hom.app _)).mp inferInstance
    apply ULift.ext
    exact Additive.toMul.injective (hv.trans (hz 0).symm)
  change ((upperStarLowerStarAdjunction _ v).homEquiv _ _
    (t.line v H).hom).hom.app U
      (finiteEtaleTateOneGenerator _ _ T hA U a (z 0)) = _
  rw [t.line_normalization, hroot]
  rfl

end AlgebraicGeometry.Etale
