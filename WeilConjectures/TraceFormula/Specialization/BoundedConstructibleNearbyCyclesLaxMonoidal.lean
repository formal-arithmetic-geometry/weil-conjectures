/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGlobal
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible

/-!

# The lax monoidal structure of nearby cycles on bounded constructible complexes

The lax monoidal structure of nearby cycles restricts to bounded constructible complexes
(`NearbyCyclesModel.boundedConstructibleNearbyCyclesLaxMonoidal`).

This is split out of `WeilConjectures.TraceFormula.Specialization.KernelPullbackDeformation` so
that the modules which only need the structure do not depend on the kernel on the deformation.

-/

@[expose] public section
universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k k' : Type u} [Field k] [Field k'] [Fact (ringChar k ≠ ℓ)]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

/-- The lax monoidal structure of nearby cycles on bounded constructible complexes. -/
@[instance_reducible]
noncomputable def boundedConstructibleNearbyCyclesLaxMonoidal
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) :
    (boundedConstructibleNearbyCycles hP).LaxMonoidal :=
  @ObjectProperty.laxMonoidalLift _ _ _ _ _ _ (boundedConstructible _) _
    (boundedConstructible _) _ (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (M.nearbyCyclesLaxMonoidal (Profinite.padicAlgClRingObj ℓ)) _

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
