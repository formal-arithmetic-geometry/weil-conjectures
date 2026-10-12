/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeSubKernel
import Sheaf.Topology.FiniteTypeSurjectiveNearStalk
import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# Local isomorphism criterion for coherent modules

Source: Stacks Project, Cohomology of Schemes, Lemma 01Y3
(blueprint: lem-weil-pbc-coherent-local-isomorphism).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
universe u
namespace AlgebraicGeometry
noncomputable section

/-- At a point of a locally Noetherian scheme, a morphism of coherent modules has
zero, injective, surjective, or bijective stalk behaviour on a neighbourhood.
Source: Stacks Project, Cohomology of Schemes, Lemma 01Y3
(blueprint: lem-weil-pbc-coherent-local-isomorphism).
Proof:
1. By `pqf-def-coherent`, both modules are of finite type, in the sense of
   `def-weil-pbc-module-finite-type-presentation`. The kernel of `φ` is computed
   sectionwise (`def-weil-sheaf-of-modules-category`), so its restriction vanishes
   exactly when every section map of `φ` on that neighbourhood is injective.
   The locally Noetherian hypothesis is retained from the source but is unused.
2. For (3), apply `lem-weil-pbc-module-finite-type-surjective-on-stalk` (Modules,
   01B8) to `φ`, since its target is of finite type.
3. A finite-type module with zero stalk vanishes near the point (Modules, 01B9):
   apply 01B8 to the zero map into it; local surjectivity says every section is
   locally zero, and the sheaf axiom makes it zero. Apply this to `F` for (1).
4. For (2), `lem-weil-pbc-coherent-finite-type-sub-kernel` makes `Ker φ` finite
   type. Its stalk is zero: represent a kernel germ by a section, use injectivity
   of `φₓ` to make its germ in `G` zero, and shrink until the section itself is
   zero (`def-weil-pbc-module-stalk`). Step 3 makes the kernel vanish near `x`.
5. For (4), intersect the neighbourhoods from (2) and (3). A target section has
   local preimages by sheaf surjectivity; injectivity makes them agree on overlaps,
   so they glue. Every section map is thus bijective. Their inverses are linear
   and commute with restriction, giving an inverse morphism of module sheaves.
-/
theorem coherent_local_isomorphism (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F G : SheafOfModules (moduleRings X.toLocallyRingedSpace.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toLocallyRingedSpace.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toLocallyRingedSpace.toRingedSpace G)
    (φ : G ⟶ F) (x : X) :
    (IsZero ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) →
      ∃ U : X.Opens, x ∈ U ∧ IsZero (F.over U)) ∧
    (Function.Injective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map φ) →
      ∃ U : X.Opens, x ∈ U ∧
        ∀ (V : X.Opens), V ≤ U →
          Function.Injective (ConcreteCategory.hom (φ.val.app (.op V)))) ∧
    (Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map φ) →
      ∃ U : X.Opens, x ∈ U ∧
        Epi ((SheafOfModules.overFunctor
          (moduleRings X.toLocallyRingedSpace.toRingedSpace) U).map φ)) ∧
    (Function.Bijective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map φ) →
      ∃ U : X.Opens, x ∈ U ∧
        IsIso ((SheafOfModules.overFunctor
          (moduleRings X.toLocallyRingedSpace.toRingedSpace) U).map φ)) := by
  sorry

end
end AlgebraicGeometry
