/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.ZetaSeries
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointPullbackTrivializationMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-! # Local operator compatibility for normalized fibre comparisons -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory.Endofunctor
open WeilConjectures.NativeCondensedModule
open scoped CategoryTheory.Obj TensorProduct
namespace WeilConjectures.CondensedFibreComparisons

/-- The actual iterate-and-return operator respects any normalized tensor and dual
comparisons, and the finite-product projections.
Source: realified-kernel proof Steps 1--2, tensor and inverse-transpose operators
(blueprint: lem-fd-condensed-fibre-local-operators).

Proof: induct on the positive exponent using the monoidal pullback compositor.
For the tensor datum this identifies the iterated map with the two iterated input
maps followed by the inverse tensorator. The canonical point trivialization is
monoidal by `point_pullback_trivialization_monoidal`; composing its inverse with
the pullback compositors and the return equality therefore preserves tensor
sections and the unit. Apply the sections functor to obtain the tensor identity
on pure tensors. The normalization in `c.tensor_sections` and linearity extend
it to every vector. The ordinary contragredient datum preserves evaluation by
the closed pullback comparison. The same induction and unit return give
(Bf)(Av)=f(v). Substitute A inverse v and use `c.dual_evaluation`; injectivity
of the coefficient-unit map gives the required inverse-transpose formula.
Naturality of iteration and of point return gives the operator equation for
every intertwining morphism. Apply it to each finite-product projection; the
additive point-sections functor preserves finite products, making piComparison
invertible. These arguments include the zero module, rank zero and empty sums.
-/
theorem local_operator_compatibility (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (g : T ≅ T) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g.hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (c : Comparisons l D g z) : WeilCompatibility l D g z n h c := by sorry

end WeilConjectures.CondensedFibreComparisons
