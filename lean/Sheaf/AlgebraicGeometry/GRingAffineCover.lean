/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import Sheaf.RingTheory.RegularRingEquiv

/-!
# G-rings on affine opens of a scheme

Source: Stacks Project, Properties of Schemes, Tag 0HA5, equivalence (3) and (2)
(blueprint: lem-trf-g-ring-affine-cover).
-/

@[expose] public section

universe u v

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false

/-- The G-ring property passes from an affine open cover to every affine open.

Source: Stacks Project, Properties of Schemes, Tag 0HA5, equivalence (3) and (2)
(blueprint: lem-trf-g-ring-affine-cover).

Proof: (1) The G-ring hypothesis says each affine chart ring is Noetherian, so the
cover gives local Noetherianity. (2) The affine-open local-Noetherianity theorem makes
the section ring of the arbitrary affine open Noetherian. (3) For each prime of that
ring, identify its localization with the corresponding localization of a covering
chart through their common stalk, using the affine-open point and stalk-localization
statements. (4) Transport the adic completion map across the resulting ring
isomorphism using the compatible-completion equivalence. (5) Transport regularity of
the chart completion map through this commuting square using invariance of regular
ring maps under ring equivalences. (6) The Noetherianity and regularity conditions
are exactly the definition of a G-ring.
-/
theorem isGRing_of_affine_open_cover
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.affineOpens)
    (hU : ⨆ i, (U i : X.Opens) = ⊤)
    (h : ∀ i, IsGRing Γ(X, U i)) (V : X.affineOpens) :
    IsGRing Γ(X, V) := by
  sorry

end AlgebraicGeometry
