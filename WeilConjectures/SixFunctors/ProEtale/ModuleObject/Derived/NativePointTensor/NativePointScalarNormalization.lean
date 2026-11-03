/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.PointFiberTensorSystem
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointTensorReduction.CondensedPointTensorReduction
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions

/-! # Normalization of the native scalar comparison

Source: latest blueprint, sec-six-functors/sk-thm-sf-kunneth-relative/_section.md,
finite-reduction and scalar-extension compatibility, specialized to Spec k.
(blueprint: lem-sf-native-point-scalar-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

attribute [local instance] Mod.extendScalarsMonoidal
attribute [local instance 20000]
  CategoryTheory.InternalAbelianSheafModule.comparison_essentiallySmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativePointTensor

/-- The scalar-adjunction comparison exists with its ordinary section formula and
its K-flat localization square. This assertion contains no tensor or unit square.

Source: relative Künneth, finite-reduction/scalar-extension clause; the native
integral, rational and closure scalar-coherence constructions, after changing the
section presentation (blueprint: lem-sf-native-point-scalar-normalization).

Proof: reconstruct each internal module as a section module and evaluate at the
terminal pro-etale object. The singleton scalar ring is identified with MonObj.Γ
by sectionGlobalEquiv, and terminal_eval identifies the two ordinary section
functors. Define the ordinary comparison by scalar adjunction: b tensor x maps to
b times the image of x under internal scalar extension, using its sheafification
unit. Its formula is natural in x. Transport the supplied integral ReductionData
and its transition data across these section equivalences for integral and finite
quotients; use the rational package for localization and the finite-subextension
package for field and closure inclusions. For integral inclusions use finite
freeness of the larger integer ring and the ambient scalar tensor comparison;
a basis proves invertibility of the specified map but does not choose it. For an
integral map specified sectionwise, extensionality identifies it with the native
quotient, so the comparison transports to that exact map. The universal property
of ordinary derived scalar extension gives the unique derived comparison
compatible with the ordinary comparison on flat-term K-flat representatives.
The representative isomorphisms in ReductionData prove it invertible, including
nonflat quotient maps. Conjugate the exact section comparison by the fixed
TraceCupPoint.exactComparison to obtain comparison on the right-derived fibre.
The defining counit equations give precisely the displayed representative square;
no tensor-coherence assertion is used here. -/
theorem native_scalar_normalization (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : IsScalarMap ell a) :
    Nonempty (ScalarComparison D.k a) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NativePointTensor
