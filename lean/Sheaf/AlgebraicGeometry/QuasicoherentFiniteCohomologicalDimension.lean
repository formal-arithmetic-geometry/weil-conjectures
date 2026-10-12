/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.AlternatingCechComputes
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray

/-!
# Finite cohomological dimension for quasi-coherent modules

Source: Stacks Project, Cohomology of Schemes, Lemma 30.4.2, Tag 01XI
(blueprint: lem-sc-picard-qcoh-finite-cd).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact scheme over a field with affine diagonal has a uniform nonnegative
bound on the cohomology of all quasi-coherent modules.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.4.2, Tag 01XI
(blueprint: lem-sc-picard-qcoh-finite-cd).

Proof: By quasi-compactness choose a finite affine open cover with `N` members.
The affine diagonal makes pairwise intersections affine
(`lem-sc-picard-affine-diagonal-intersections`), hence all finite intersections affine
by induction. The alternating Cech complex computes Cech cohomology
(`lem-pc-alternating-cech-computes`). Its degree `p` term is indexed by strictly increasing
`(p + 1)`-tuples of cover indices, so it is zero when `p ≥ N`. Cech comparison
(`lem-pc-cech-computes`) identifies this cohomology with `H^p(X,F)` for every
quasi-coherent module `F`. For nonempty `X`, take `d = N - 1`. For empty `X`, all
cohomology vanishes and `d = 0` suffices. The cover, and therefore the bound, is
independent of `F`. -/
theorem exists_quasicoherent_cohomology_bound (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (X ↘ Spec (.of k)))] :
    ∃ d : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), d < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
