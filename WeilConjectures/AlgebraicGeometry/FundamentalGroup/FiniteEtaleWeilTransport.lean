/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.GroupTheory.WeilGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Separable
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import Mathlib.CategoryTheory.Filtered.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit

/-!
# Weil transport on finite étale fibres

Source: Stacks Project, Fundamental Groups, Tags 0BN5, 0BND, 0BTV and 0BTX; the finite-stage
argument in the current blueprint proof of lem-wf-finite-constant-h1-pi1
(blueprint: lem-wf-finite-etale-weil-transport).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The canonical map on the full automorphism groups of the geometric fibre functors.
It restricts an automorphism to base-changed covers and conjugates by the canonical fibre
identification; no choice of path is made. Source: Stacks Tag 0BND(3), construction of 0BN5
(blueprint: lem-wf-finite-etale-weil-transport). -/
noncomputable def fiberAutBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (g : Aut (fiber s)) : Aut (fiber (s ≫ f)) :=
  (pullbackFiberIso f s).symm ≪≫ Functor.isoWhiskerLeft (pullback f) g ≪≫ pullbackFiberIso f s

end AlgebraicGeometry.Scheme.FiniteEtale
