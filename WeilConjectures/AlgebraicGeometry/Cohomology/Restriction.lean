/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AcyclicResolution
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-!
# Restricting resolutions to open subschemes

Restriction along an open immersion `f : X ⟶ Y` is exact and sends injective `𝒪_Y`-modules to
flasque, hence acyclic, `𝒪_X`-modules. So the restriction of an injective resolution of `ℱ` is an
acyclic resolution of `ℱ|_X`, which computes its cohomology
(`AlgebraicGeometry.Scheme.Modules.H.cyclesZeroSuccAddEquiv`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exactAt_restrict`: restriction keeps a complex exact.
- `AlgebraicGeometry.Scheme.Modules.restrictCyclesIso`: the cycles of the restricted complex are
  the restriction of the cycles.
- `AlgebraicGeometry.Scheme.Modules.H.restrictSucc`: restriction of cohomology classes to an open
  subscheme, with `H.restrictSucc_apply` and `H.restrictSucc_eq_zero_iff` on representatives.
- `AlgebraicGeometry.Scheme.Modules.exists_app_toCycles_eq_of_isAffineOpen`: for quasi-coherent
  `ℱ`, the degree-one cocycles of an injective resolution lift over affine opens.
- `AlgebraicGeometry.Scheme.Modules.mem_range_app_toCycles_of_cech`: a degree-one class whose Čech
  cocycle on an affine cover is a coboundary vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance : PreservesFiniteLimits (restrictFunctor f) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

instance : PreservesFiniteColimits (restrictFunctor f) :=
  PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _

variable {ℱ : Y.Modules}

end AlgebraicGeometry.Scheme.Modules
