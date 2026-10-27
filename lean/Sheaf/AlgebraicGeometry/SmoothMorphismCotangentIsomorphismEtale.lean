/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap

/-!
# The cotangent criterion for a morphism between smooth schemes

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 2.2 Corollary 10, p. 41;
Stacks Project, Tag 02GU, condition (8), on smooth charts
(blueprint: lem-sfb-smooth-morphism-cotangent-isomorphism-etale).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An S-morphism between smooth S-schemes is étale near x exactly when its canonical
relative differential map is an isomorphism on the stalk at x. The equality g ≫ q = p
identifies the target of the existing canonical differential map with Ω(X/S).
No field, Noetherian, separatedness or constant-dimension assumption is made.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 2.2 Corollary 10, p. 41;
Stacks Project, Tag 02GU, condition (8), on smooth charts
(blueprint: lem-sfb-smooth-morphism-cotangent-isomorphism-etale).

Proof: apply the pointwise clause of lem-sfb-smooth-cotangent-etale-criterion to
S, X, Y with structure maps p, q and h = g. The equation g ≫ q = p is precisely
its S-morphism hypothesis. Its differential dh is the canonical map used here:
both send a ⊗ db to a d(g-sharp b), by the universal derivation characterization.
The pointwise equivalence is therefore exactly the displayed equivalence at x.
Only smoothness over S is needed; the equal-rank assumption in the cited node
belongs solely to its additional determinant clause and is not used here. -/
theorem smooth_morphism_cotangent_isomorphism_etale {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (g : X ⟶ Y) (h : g ≫ q = p)
    [Smooth p] [Smooth q] (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ g)) ↔
      IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (q.relativeDifferentialsPullbackMap g ≫
          (Scheme.Hom.relativeDifferentialsCongr (g ≫ q) h).hom)) := by
  sorry

end AlgebraicGeometry
