/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasi-coherent modules annihilated by a closed subscheme's ideal

Source: Stacks Project, Morphisms, Lemma 01QY, and Modules, Lemmas 08KS,
01BG, and 01B6 (blueprint: lem-weil-pbc-closed-immersion-pushforward-annihilated).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Pushforward from a closed subscheme preserves quasi-coherence and is annihilated by
its ideal. A quasi-coherent module annihilated by that ideal has quasi-coherent pullback
and invertible canonical unit, and finite type passes to that pullback.
Here `i.ker.idealOfOpens V` is the ideal on every open, not only affine opens.
Source: Stacks Project, Morphisms, Lemma 01QY, and Modules, Lemmas 08KS, 01BG, and 01B6
(blueprint: lem-weil-pbc-closed-immersion-pushforward-annihilated).
Proof, following the node's seven steps:
1. A closed immersion is finite, hence affine (lem-weil-pbc-closed-immersion-finite).
Apply lem-weil-pbc-affine-pushforward-base-change (1) to obtain quasi-coherence.
2. The action on pushforward sections is restricted along `i.app V`; elements of its
kernel act by zero (def-pc-module-pullback, def-sbc-closed-immersion-ideal-sheaf).
3. Pullback preserves quasi-coherence (lem-weil-pbc-module-pullback-quasi-coherent)
and finite type (lem-weil-pbc-support-pullback-finite-type (3)).
4. Test the unit on stalks (lem-weil-pbc-module-iso-on-stalks). Off the closed image,
the target is zero by lem-weil-pbc-closed-pushforward-stalks; the source is zero because
the ideal is the unit ideal on the complementary open.
5. At `x = i(z)` the local ring map is surjective by
lem-weil-pbc-locally-surjective-iff-stalks and lem-weil-pbc-closed-pushforward-stalks.
Its kernel kills the source stalk: shrink representatives until their images vanish,
then apply the sectionwise annihilation hypothesis (def-weil-pbc-module-stalk).
6. Using lem-weil-pbc-module-stalk-pullback and the closed pushforward stalk comparison,
the unit is `M → M ⊗ R/I`, `m ↦ m ⊗ 1`. Its inverse sends `m ⊗ b` to a lift of `b`
acting on `m`; independence of the lift follows from `IM = 0`.
7. The stalkwise isomorphisms give the module isomorphism by
lem-weil-pbc-module-iso-on-stalks. -/
theorem closedImmersion_pushforward_annihilated
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (∀ (G : Z.Modules) [G.IsQuasicoherent],
      ((pushforward i).obj G).IsQuasicoherent ∧
        ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ i.ker.idealOfOpens V →
          ∀ s : Γ((pushforward i).obj G, V), a • s = 0) ∧
      ∀ (F : X.Modules) [F.IsQuasicoherent],
        (∀ (V : X.Opens) (a : Γ(X, V)), a ∈ i.ker.idealOfOpens V →
          ∀ s : Γ(F, V), a • s = 0) →
          ((tensorPullback i).obj F).IsQuasicoherent ∧
            IsIso ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app F) ∧
              (F.IsFiniteType → ((tensorPullback i).obj F).IsFiniteType) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
