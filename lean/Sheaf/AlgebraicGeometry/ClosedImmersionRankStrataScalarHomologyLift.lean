/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Algebra.Homology.DerivedOpenShriekAdjunction
import Sheaf.Algebra.Homology.ModuleStalkExact

/-! # Lifting scalar maps from one closed rank support

Source: Stacks Tags 0BQZ, 08BS, 08BT; rank-support reconstruction step 2.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

/-- A scalar map from one closed rank support lifts to the derived object when
its other cohomology degrees are supported on the other rank strata.

Source: Stacks, Tag 0BQZ (single-degree truncation), and Cohomology, Tags
08BS and 08BT (exact extension by zero and its adjunction).
(blueprint: lem-sc-closed-immersion-rank-strata-scalar-homology-lift)

Proof: For negative n the source is zero, and the zero morphism is a lift.
Otherwise let V be the complement in Y of the closed image of the complement
of the rank-n stratum. On V every other cohomology degree vanishes: its
support is a different rank stratum. Exact restriction therefore gives a
single-degree derived object. The canonical truncation isomorphism identifies
it with its degree-n homology placed in degree n, compatibly with homology.
Restrict a and compose with the inverse truncation isomorphism. Extension
by zero is exact and left adjoint to restriction, so this local morphism
extends to a morphism into K. The source sheaf is supported on the closed
image of the rank-n stratum, which is contained in V; hence the counit
from the extension by zero of its restriction is an isomorphism, as is
checked on stalks. Use this isomorphism to identify the extended source
with the original source. The homology of the resulting morphism is a:
on V this follows from the truncation comparison and counit naturality,
and off V both maps have zero source stalk. Equality of sheaf morphisms
is detected on stalks. Empty strata give zero source; no finiteness or
algebra action is used. -/
theorem closedImmersion_rankStrata_scalar_homology_lift
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings Y.toRingedSpace))]
    (r : LocallyConstant Z ℕ)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (n : ℤ)
    (hother : ∀ m : ℤ, m ≠ n → Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) m).obj K ≅
        (Scheme.Modules.pushforward i).obj (T m)))
    (a : (Scheme.Modules.pushforward i).obj (T n) ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj K) :
    ∃ f : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj
          ((Scheme.Modules.pushforward i).obj (T n)) ⟶ K,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).inv.app
          ((Scheme.Modules.pushforward i).obj (T n)) ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).map f = a := by sorry

end AlgebraicGeometry
