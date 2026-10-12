/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Common local ranks for a pulled-back module

Source: Stacks Project, Tags 0BDP and 01E8.
(blueprint: lem-sc-picard-pullback-local-ranks)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A pulled-back finite locally free module and its two direct images have one
common finite rank locally after every change of base.
Source: Stacks Project, Tag 0BDP, projection-formula paragraph, using Tag 01E8.
(blueprint: lem-sc-picard-pullback-local-ranks)

Proof: For h : T' → T, form the canonical map X_{T'} → X_T by the pullback
universal property. The composition isomorphisms of tensor pullback and the
commutative projection squares transport e to q'^*E ≅ p'^*h^*N. Finite locally
free modules remain finite locally free under pullback: pull back their finite
local frames. In such frames the dual is the coordinate dual free module, and
pullback of the dual identifies with the dual of the pullback. Thus also
q'^*(E^dual) ≅ p'^*((h^*N)^dual). The finite-locally-free unit theorem for p',
using hO at h ≫ g, identifies the two direct images with h^*N and its dual.
Choose an open U containing t on which h^*N has a finite frame of size r.
Its coordinate dual frame has the same size. Transport these frames across the
two direct-image identifications and restrict to U. Pulling the original frame
up to X_U gives q_U^*E a frame of size r too. These three frames give exactly
the three displayed fixed-rank predicates. Empty T' has no point to check;
the empty frame handles r = 0, including an empty X_U. -/
theorem picard_pullback_local_ranks {X S T : Scheme.{u}}
    (f : X ⟶ S)
    (hO : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g'))).unit.app
          (SheafOfModules.unit T'.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S) (N : T.Modules) [N.IsFiniteLocallyFree]
    (e : Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj E ≅
      (Modules.tensorPullback (pullback.snd f g)).obj N)) :
    ∀ {T' : Scheme.{u}} (h : T' ⟶ T) (t : T'),
      ∃ U : T'.Opens, t ∈ U ∧ ∃ r : ℕ,
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback U.ι).obj
            ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
              ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj E))) r ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback U.ι).obj
            ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
              ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj
                (Modules.dual E)))) r ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback (pullback.fst f (U.ι ≫ h ≫ g))).obj E) r := by sorry

end AlgebraicGeometry.Scheme
