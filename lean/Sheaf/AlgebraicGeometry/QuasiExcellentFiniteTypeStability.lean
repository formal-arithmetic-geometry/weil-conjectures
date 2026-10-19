/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.Topology.Defs.Filter
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.RingTheory.FiniteTypeGRing
import Sheaf.AlgebraicGeometry.GRingAffineCover
import Sheaf.AlgebraicGeometry.JTwoAffineCover
import WeilConjectures.RingTheory.GRing

/-!
# Quasi-excellence under locally finite-type morphisms

Source: Stacks Project, More on Algebra, Tag 07QU; Morphisms, Tags 0HAC and 0HAB;
Properties of Schemes, Tag 01OV
(blueprint: lem-per-quasi-excellent-finite-type-stability).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme locally of finite type over a scheme with quasi-excellent affine coordinate
rings again has quasi-excellent affine coordinate rings. If its underlying space is
quasi-compact, it has a finite affine open cover by Noetherian coordinate rings, the
finite-cover characterization of a Noetherian scheme.

Source: Stacks Project, Tags 07QU, 0HAC, 0HAB and 01OV
(blueprint: lem-per-quasi-excellent-finite-type-stability).

Proof:
1. Cover the target by affine opens and refine their inverse images by affine opens
   using `def-weil-finite-type-morphism` and `def-pc-scheme`. Each coordinate algebra
   is finite type over a quasi-excellent target coordinate ring; the cover need not be finite.
2. Apply `lem-weil-pbc-finite-type-algebra-noetherian` and
   `lem-weil-pbc-finite-type-over-g-ring` to these algebras. They are Noetherian G-rings;
   no injectivity or universal catenarity is required.
3. Each chart algebra is J-2: any finite type algebra over it is finite type over the
   target ring, by adjoining the two finite lists of generators from
   `def-weil-pbc-finite-type-algebra`. Its regular locus is therefore open by the
   target ring's J-2 condition in `def-exc-excellent-ring`.
4. The cover gives local Noetherianity by `pqf-def-locnoeth`. Apply
   `lem-trf-g-ring-affine-cover` and then `lem-trf-j2-affine-cover` to obtain the G-ring
   and J-2 conditions on every affine open. The former includes Noetherianity by
   `def-weil-pbc-g-ring`; no affine-intersection or separatedness assumption is needed.
5. These conditions reassemble to quasi-excellence by `def-exc-excellent-ring`.
   No dimension bound or universal catenarity has been used.
6. If the source is quasi-compact, `def-weil-pbc-quasi-compact-scheme` supplies a
   finite subcover of the chart cover. Its coordinate rings are Noetherian by step 2,
   giving the stated cover, with `n = 0` allowed for the empty scheme.
-/
theorem quasiExcellent_affineOpens_of_locallyOfFiniteType
    {X Y : Scheme.{u}} (h : X ⟶ Y) [LocallyOfFiniteType h]
    (hY : ∀ V : Y.affineOpens, IsQuasiExcellent Γ(Y, V)) :
    (∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U)) ∧
      (CompactSpace X → ∃ (n : ℕ) (U : Fin n → X.affineOpens),
        (⨆ i : Fin n, (U i : X.Opens)) = ⊤ ∧
          ∀ i : Fin n, IsNoetherianRing Γ(X, U i)) := by
  sorry

end AlgebraicGeometry
