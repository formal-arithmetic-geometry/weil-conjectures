/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPullback.NativeCondensedPullbackFrobenius
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCurveLisseDescent
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.Defs.Filter
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Analysis.Normed.Algebra.Ultra
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Mathlib.Order.CompletePartialOrder
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # A common real weight from an anchor and pure curve tests

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraphs 1--4
(blueprint: lem-zl-real-mixed-anchor-weight).

The curve record only bundles the geometric curve in the hypothesis. Its pullback is the
existing native condensed Weil pullback, and its power predicate uses the canonical fibre
comparison. No arbitrary Frobenius map or replacement coefficient model is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.RealMixedAnchor
open NativeL2 NativeCondensedModule NativeCondensedPullback

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

/-- A smooth geometrically connected affine curve embedded in the finite constant base change.
The arithmetic arrow is over k₀; its canonical lift to X₀ × k_m is a closed immersion.
Source: latest blueprint, paragraph 2 (blueprint: lem-zl-real-mixed-anchor-weight). -/
structure Curve (m : ℕ) (hm : 1 ≤ m) where
  model : Over (Spec (.of (constantExtensionDatum D m hm).k₀))
  [finiteType : LocallyOfFiniteType model.hom]
  [quasiCompact : QuasiCompact model.hom]
  [separated : IsSeparated model.hom]
  [affine : IsAffine model.left]
  [smooth : SmoothOfRelativeDimension 1 model.hom]
  [connected : GeometricallyConnected model.hom]
  arithmetic : Over.mk (model.hom ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ X₀
  embedded : IsClosedImmersion (pullback.lift arithmetic.left model.hom arithmetic.w)

attribute [instance] Curve.finiteType Curve.quasiCompact Curve.separated Curve.affine
  Curve.smooth Curve.connected

end WeilConjectures.RealMixedAnchor
