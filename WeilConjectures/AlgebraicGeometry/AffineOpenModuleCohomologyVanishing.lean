/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.Topology.OpenModuleCohomology
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyComparison

/-! # Vanishing of higher module cohomology on affine opens

Source: Stacks Project, Cohomology of Schemes, Lemma 30.2.2, Tag 01XB.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-coherent module has zero positive-degree cohomology on every affine open
(Stacks, Tag 01XB). -/
theorem subsingleton_openModuleCohomology_of_isAffineOpen (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (p : ℕ) (hp : 0 < p) :
    Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  let : IsAffine U.toScheme := hU
  let G := (Scheme.Modules.restrictFunctor U.ι).obj F
  have : Subsingleton (G.H (q + 1)) :=
    Scheme.Modules.subsingleton_H_succ_of_isAffine G q
  obtain ⟨e⟩ := nonempty_openModuleCohomology_addEquiv_restrict_H X F U (q + 1)
  exact ⟨fun x y ↦ e.injective (Subsingleton.elim (e x) (e y))⟩

end AlgebraicGeometry
