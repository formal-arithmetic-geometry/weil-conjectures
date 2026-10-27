/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

/-! # Central action on ordinary derived condensed invariants

Source: main-20261015 blueprint, six-functors direct-image stability proof, paragraph (3),
agent-extracted dense-lattice analytic input; Stacks Derived Categories, Tags 05TH, 05TI,
070Y, 070K and 0159 (blueprint: lem-sfb-central-action-derived-vanishing).

The central operator is uniquely specified on every profinite section, so its construction
selects no unspecified module map. The derived functor is the recorded ordinary total
right derived invariants functor, without a continuous-cochain comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar

namespace CategoryTheory.CondensedDerivedRestriction

variable {A : CondensedBar.Ring.{u}} {J : Type u} [Group J] [TopologicalSpace J]
  [IsTopologicalGroup J]

/-- Constant central action determines a unique equivariant internal-module endomorphism.
Source: direct-images proof paragraph (3), dense-lattice input, central-action step 1
(blueprint: lem-sfb-central-action-derived-vanishing).
Proof: on every test object S use N.act S at the constant map of value z. Each component
is R(S)-linear, and action naturality makes these components commute with restriction.
The section-module equivalence therefore gives an internal-module map. For every
continuous g : S → J, pointwise centrality gives c_z g = g c_z; the action's multiplicative
law makes this map equivariant. The faithful underlying-sheaf functor and equality of all
section maps give uniqueness. The same equivariance equation for any morphism makes the
operators natural in N, so they commute with resolution differentials and augmentations. -/
theorem existsUnique_centralAction (N : Equivariant A J) (z : J)
    (hz : ∀ g : J, z * g = g * z) :
    ∃! f : N ⟶ N, ∀ (S : Profinite.{u})
      (m : Profinite.CondensedAction.sectionModule A.toMon N.module S),
      (f.val.hom.hom.app (op S)).hom m = N.act S (ContinuousMap.const S z) m := by
  sorry

/-- The central operator with its uniquely specified constant-action section maps.
The existence theorem determines the map uniquely, rather than choosing arbitrary data.
Source: direct-images proof paragraph (3), dense-lattice central-action step 1
(blueprint: lem-sfb-central-action-derived-vanishing). -/
def centralAction (N : Equivariant A J) (z : J) (hz : ∀ g : J, z * g = g * z) : N ⟶ N :=
  Classical.choose (existsUnique_centralAction N z hz)

/-- The central operator acts by the constant generalized group element on every section.
Source: direct-images proof paragraph (3), dense-lattice central-action step 1
(blueprint: lem-sfb-central-action-derived-vanishing).
Proof: the chosen map satisfies the section formula by the existence-and-uniqueness
specification; substitute the definition of centralAction into that specification. -/
theorem centralAction_apply (N : Equivariant A J) (z : J)
    (hz : ∀ g : J, z * g = g * z) (S : Profinite.{u})
    (m : Profinite.CondensedAction.sectionModule A.toMon N.module S) :
    ((centralAction N z hz).val.hom.hom.app (op S)).hom m =
      N.act S (ContinuousMap.const S z) m := by
  sorry

/-- Central action becomes identity in the ordinary derived category; an invertible
central-action difference forces the entire derived invariant object to be zero.
Source: direct-images proof paragraph (3), dense-lattice analytic input; Stacks Tags
05TH, 05TI, 070Y, 070K and 0159
(blueprint: lem-sfb-central-action-derived-vanishing).
Proof:
1. The central section operators are equivariant and natural, by the constant-action
   construction above (def-sfb-condensed-action-module).
2. Resolve N[0] equivariantly by a bounded-below complex I of injectives, hence K-injectives
   (lem-sfb-condensed-action-injective-infrastructure). The ordinary total right-derived
   computation unit is invertible at I. Naturality gives z_I s = s z_N[0].
3. Fully fixed sections are fixed under c_z at the identity base change. Since the
   invariants inclusion is sectionwise injective, invariants of z_I are the identity
   chain map (def-sfb-condensed-action-module).
4. Naturality of the computation unit of def-sfb-right-derived-functor and its
   invertibility at I show RΓ(z_I) = id. Apply the derived functor to z_I s = s z_N[0]
   and cancel the invertible image of the resolution quasi-isomorphism s.
5. Additivity gives RΓ((z_N-id)[0]) = 0. If z_N-id is invertible, its derived image is
   invertible. Composing its inverse with zero gives id = 0. Every map to or from the
   derived invariant object is consequently zero, so it is both initial and terminal.
No assumption on triviality, dimension, compactness or discreteness is used. -/
theorem centralAction_derived_vanishing (N : Equivariant A J) (z : J)
    (hz : ∀ g : J, z * g = g * z) :
    (derived A J).map
        ((DerivedCategory.singleFunctor (Equivariant A J) 0).map (centralAction N z hz)) =
      𝟙 ((derived A J).obj ((DerivedCategory.singleFunctor (Equivariant A J) 0).obj N)) ∧
    (IsIso (centralAction N z hz - 𝟙 N) →
      IsZero ((derived A J).obj ((DerivedCategory.singleFunctor (Equivariant A J) 0).obj N))) := by
  sorry

end CategoryTheory.CondensedDerivedRestriction
