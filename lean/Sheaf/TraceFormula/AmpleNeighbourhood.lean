/-
Copyright (c) 2026 Q78. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q78
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent
import Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.LimitFibreProducts
import Sheaf.AlgebraicGeometry.LimitResidueField
import Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood
import WeilConjectures.AlgebraicGeometry.ProperLimitNoetherian
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Ample invertible modules near a fibre

Source: Stacks Project, More on Morphisms, Lemma 0D2S (blueprint: lem-trf-ample-neighbourhood).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/--
Source: Stacks Project, More on Morphisms, Lemma 0D2S
(blueprint: lem-trf-ample-neighbourhood).

If an invertible module on a proper scheme is ample on one fibre, it is ample after
restricting to the inverse images of affine opens in a neighbourhood of the base point.
The proof uses affine Noetherian approximation, descent of invertible modules and fibrewise
ampleness, and openness of ampleness in the Noetherian case; these are recorded in the
proof steps of the corresponding DAG node.
-/
theorem exists_ample_neighbourhood {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (L : Y.Modules) [L.IsInvertible] (x : X) :
    Scheme.Modules.IsAmple (f.fiber x) ((Scheme.Modules.pullback (f.fiberι x)).obj L) →
      ∃ U : X.Opens, x ∈ U ∧ CompactSpace ((f ⁻¹ᵁ U).toScheme) ∧
        ∀ V : X.Opens, V ≤ U → IsAffineOpen V →
          Scheme.Modules.IsAmple ((f ⁻¹ᵁ V).toScheme)
            ((Scheme.Modules.pullback ((f ⁻¹ᵁ V).ι)).obj L) := by
  sorry

end AlgebraicGeometry
