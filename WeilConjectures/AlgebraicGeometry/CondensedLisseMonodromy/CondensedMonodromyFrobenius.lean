/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy.CondensedLisseMonodromy
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.GroupTheory.WeilGroup
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import Mathlib.CategoryTheory.Filtered.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.DescendFinite
public import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
public import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit
public import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RepresentationTheory.Invariants
import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy

/-! # Condensed geometric sections and local Frobenius

Source: latest blueprint, sec-purity-real-sheaves/sk-lem-wrp-hc2/p-real-sections.md,
its residual-Frobenius paragraph, and sk-lem-wrp-hc2.proof.md, final paragraph
(blueprint: lem-a1-condensed-monodromy-frobenius).

The auxiliary declarations spell out the arrows in the assertion. `FibreAssertions`
records the representation, sections, naturality, tensor and dual clauses;
`ArithmeticAssertions` fixes the arithmetic normalization and the actual local-return
operator. The theorem asserts their existence over the given finite-field scheme.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseMonodromy

/-- The projection to the finite-field model in geometric coordinates.
Source: def-wf-weil-group, base-change convention
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
def modelProjection (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {X : Scheme.{u}} (j : X ≅ (D.geometricFiber X₀).left) : X ⟶ X₀.left :=
  j.hom ≫ pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The existing Weil group, using the arithmetic image of the geometric base point.
Source: def-wf-weil-group
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
abbrev ModelWeilGroup (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [GeometricallyConnected X₀.hom] {X : Scheme.{u}}
    (j : X ≅ (D.geometricFiber X₀).left)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :=
  FiniteEtale.weilGroup X₀.hom (t ≫ modelProjection D X₀ j)
    (Aut (FiniteEtale.fiber (t ≫ modelProjection D X₀ j)))

/-- The existing degree homomorphism, without rescaling its integer grading.
Source: lem-wf-weil-group-exact-sequence
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
abbrev modelDegree (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [GeometricallyConnected X₀.hom] {X : Scheme.{u}}
    (j : X ≅ (D.geometricFiber X₀).left)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :=
  FiniteEtale.weilGroupDeg X₀.hom (t ≫ modelProjection D X₀ j)
    (Aut (FiniteEtale.fiber (t ≫ modelProjection D X₀ j)))

end AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
