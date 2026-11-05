/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FilteredColimit.LowerStar

/-!
# Continuity of derived pushforwards along a Galois tower

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) and `K` a bounded
below complex of `Λ_X`-module objects, `Λ = C(-, T₀)` for a finite discrete ring `T₀`. The
complexes `g_{j*} g_j^* K` of the finite levels form a filtered diagram with a cocone to
`g_{∞*} g_∞^* K` (`AlgebraicGeometry.ProEtale.GaloisTower.complexDiagram`,
`AlgebraicGeometry.ProEtale.GaloisTower.complexCocone`), which is a colimit when it is so termwise
(`AlgebraicGeometry.ProEtale.GaloisTower.isColimitComplexCocone`). For a quasi-compact
quasi-separated `f : X ⟶ Z`, the cohomology sheaves of `Rf_*` of `g_{∞*} g_∞^* K` are then the
filtered colimits of those of the finite levels
(`AlgebraicGeometry.ProEtale.GaloisTower.isColimit_homology_rightDerivedLowerStar_complexCocone`):
the continuity of `Rf_* (g_{∞*} g_∞^*)` along the tower.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable (K : CochainComplex
  (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)

end AlgebraicGeometry.ProEtale.GaloisTower
