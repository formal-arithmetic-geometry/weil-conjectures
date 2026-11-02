/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

public import WeilConjectures.CategoryTheory.InverseMateEquivalence

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj

/-! # Data for the rational affine-line trace over the ground field

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/sk-thm-inversion/
lem-fd-first-formula.proof.md, constant-sheaf paragraph, and
sk-lem-wft-character-integral/lem-fd-character-integral.proof.md, coefficients paragraph.
(blueprint: def-fd-rational-affine-line-trace-data).

The target uses the recorded internal signed Tate line in degree two. Its pullback
is transported from the recorded signed comparison, including its evaluation
normalization. No roots of unity or trivialization over k are chosen.

## Main definitions and statement

- `negative`: the recorded internal signed Tate line, shifted by [-2].
- `compactSupport`: the actual affine-line compact-support coefficient object.
- `exchange`: the actual proper/open compact-support exchange on that object.
- `primeFieldMap`: the canonical map to the prime field.
- `primePullbackComp`: the published derived pullback compositor at that map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u vA vB vC vD uA uB uC uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalAffineLineTrace

open CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

section NativeTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
end NativeTransport

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The compact-support input is bounded constructible over every base scheme.
Source: the native coefficient unit is free of rank one in degree zero
(blueprint: def-fd-rational-affine-line-trace-data).
Proof: apply the proved native bounded-constructibility theorem for the derived tensor unit.
The displayed `unit` uses exactly that monoidal structure. -/
theorem boundedConstructible_unit (X : Scheme.{u}) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)
      (unit ℓ E X) := by
  exact boundedConstructible_tensorUnit (Profinite.continuousMapRingObj E.1) X

/-- The canonical homomorphism from the prime field, named before applying Spec.
Source: the prime-field structure map in the line-trace argument
(blueprint: def-fd-rational-affine-line-trace-data). -/
def primeFieldEmbedding (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] : ULift.{u} (ZMod p) →+* k :=
  (ZMod.castHom dvd_rfl k).comp ULift.ringEquiv.toRingHom

/-- The canonical structure morphism to the prime field.
Source: prime-field base change in the affine-line trace proof
(blueprint: def-fd-rational-affine-line-trace-data). -/
def primeFieldMap (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] :
    Spec (.of k) ⟶ Spec (.of (ULift.{u} (ZMod p))) :=
  Spec.map (CommRingCat.ofHom (primeFieldEmbedding p k))

/-- Prime-field structure maps commute with field homomorphisms.
Source: uniqueness of a ring map out of the prime field
(blueprint: def-fd-rational-affine-line-trace-data). -/
theorem primeFieldMap_comp (p : ℕ) [Fact p.Prime] (k k' : Type u) [Field k] [Field k']
    [CharP k p] [CharP k' p] (φ : k →+* k') :
    Spec.map (CommRingCat.ofHom φ) ≫ primeFieldMap p k = primeFieldMap p k' := by
  unfold primeFieldMap primeFieldEmbedding
  rw [← Spec.map_comp]
  congr 2
  ext ⟨x⟩
  exact congrArg (fun f : ZMod p →+* k' ↦ f x)
    (RingHom.ext_zmod (φ.comp (ZMod.castHom dvd_rfl k)) (ZMod.castHom dvd_rfl k'))

/-- The published pullback compositor, with its endpoint identified by prime-field
uniqueness. Source: derived inverse-image coherence
(blueprint: def-fd-rational-affine-line-trace-data). -/
def primePullbackComp (p : ℕ) [Fact p.Prime] (k k' : Type u) [Field k] [Field k']
    [CharP k p] [CharP k' p] (φ : k →+* k') :
    moduleObjectDerivedPullback (Profinite.continuousMapRingObj E.1) (primeFieldMap p k') ≅
      moduleObjectDerivedPullback (Profinite.continuousMapRingObj E.1) (primeFieldMap p k) ⋙
        moduleObjectDerivedPullback (Profinite.continuousMapRingObj E.1)
          (Spec.map (CommRingCat.ofHom φ)) :=
  eqToIso (congrArg (moduleObjectDerivedPullback (Profinite.continuousMapRingObj E.1))
    (primeFieldMap_comp p k k' φ).symm) ≪≫
      CondensedRing.leftDerivedUpperStarComp (Profinite.continuousMapRingObj E.1)
        (Spec.map (CommRingCat.ofHom φ)) (primeFieldMap p k)

end AlgebraicGeometry.ProEtale.RationalAffineLineTrace
