/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
import WeilConjectures.AlgebraicGeometry.GroupScheme.LieCotangentDual
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Lie dimension and the local ring at a smooth identity
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

/-- The Lie algebra of a smooth group scheme has the dimension of its local ring at the identity. -/
theorem finrank_lie_eq_localKrullDim_of_smooth
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] :
    (Module.finrank k (Lie G) : WithBot ℕ∞) =
      ringKrullDim (G.left.presheaf.stalk
        (unitSection G (IsLocalRing.closedPoint k))) := by
  let R := G.left.presheaf.stalk (unitSection G (IsLocalRing.closedPoint k))
  have : IsRegularLocalRing R :=
    Smooth.isRegularLocalRing_stalk G.hom (unitSection G (IsLocalRing.closedPoint k))
  let r := identityResidueEquiv G
  let : RingHomInvPair r.toRingHom r.symm.toRingHom := RingHomInvPair.of_ringEquiv r
  let : RingHomInvPair r.symm.toRingHom r.toRingHom :=
    RingHomInvPair.of_ringEquiv r.symm
  have hdim : Module.finrank k (Lie G) =
      Module.finrank (IsLocalRing.ResidueField R)
        (Module.Dual (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) := by
    exact congrArg Cardinal.toNat
      (rank_eq_of_equiv_equiv r (lieCotangentDualEquiv G).toAddEquiv r.bijective
        (fun c v ↦ (lieCotangentDualEquiv G).map_smulₛₗ c v))
  rw [hdim, Subspace.dual_finrank_eq]
  exact (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance

end AlgebraicGeometry.GrpObj
