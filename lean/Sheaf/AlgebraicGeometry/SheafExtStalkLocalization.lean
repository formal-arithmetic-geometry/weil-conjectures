/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.SheafExt
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic

/-!
# Stalk localization of sheaf Ext

Source: Stacks Project, Tag 0FZ3, proof of (1), using Tags 0GM8, 08E8 and 0A64
(blueprint: lem-sc-ext-stalk-localization).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- Sheaf Ext between coherent modules on a Noetherian scheme has stalks equal to Ext
of their stalk modules over the local ring.
Source: Stacks Project, Tag 0FZ3, proof of (1), using Tags 0GM8, 08E8 and 0A64
(blueprint: lem-sc-ext-stalk-localization).

Proof:
1. Apply lem-sc-derived-internal-hom-stalk-localization to F and G in degree zero.
   Coherence of F on the Noetherian scheme makes F[0] pseudo-coherent by Tag 08E8;
   G[0] is bounded below. Tag 0GM8 (2) identifies the stalk of derived internal Hom
   with derived Hom over the local ring. Exactness of stalks commutes with cohomology.
2. By def-weil-pbc-sheaf-ext, the left-hand cohomology stalk is sheaf Ext in degree q.
3. By lem-sc-rhom-cohomology-ext-ring (Tag 0A64), the right-hand cohomology is Ext
   of F_x and G_x in degree q, as defined in def-pc-ext. Both identifications respect
   the local-ring action, so their composite is the displayed linear equivalence.

Natural degrees parametrize exactly the integers q >= 0. The derived-category instance
is size infrastructure for the recorded sheaf Ext definition. -/
theorem nonempty_moduleSheafExt_stalk_linearEquiv (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F G : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (x : X) (q : ℕ) :
    Nonempty (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (moduleSheafExt X (q : ℤ) F G)) ≃ₗ[X.presheaf.stalk x]
        Abelian.Ext ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G) q) := by
  sorry

end AlgebraicGeometry
