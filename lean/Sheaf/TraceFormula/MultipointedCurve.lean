/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.PureDimension

/-! # Multipointed relative curves

Source: Temkin, *Stable modification of relative curves*, §1.2 and §3.1
(blueprint: def-trf-multipointed-curve).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A multipointed relative curve consists of a flat finitely presented curve,
its flat finitely presented zero-dimensional marking, and a closed immersion
of the marking into the curve.  Empty markings and nonseparated curves are
allowed.  Pure relative dimensions are expressed fibrewise using
`Scheme.IsPureDimension`.
Source: Temkin, *Stable modification of relative curves*, §1.2 and §3.1
(blueprint: def-trf-multipointed-curve). -/
structure MultipointedCurve (T : Scheme.{u}) where
  X : Scheme.{u}
  D : Scheme.{u}
  x : X ⟶ T
  d : D ⟶ T
  i : D ⟶ X
  comm : d = i ≫ x
  flat_X : Flat x
  lfp_X : LocallyOfFinitePresentation x
  qc_X : QuasiCompact x
  qs_X : QuasiSeparated x
  pure_X : ∀ (t : T), (x.fiber t).IsPureDimension 1
  flat_D : Flat d
  lfp_D : LocallyOfFinitePresentation d
  qc_D : QuasiCompact d
  qs_D : QuasiSeparated d
  pure_D : ∀ (t : T), (d.fiber t).IsPureDimension 0
  closed : IsClosedImmersion i

end AlgebraicGeometry
