/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogEtaleRestrictionStalkComparison
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters

/-!
# Descent of specified parameters from a geometric strict-local ring

Source: Stacks, Tags 06LN, 07QM, 00KU and 00DV
(blueprint: lem-trf-strict-local-parameter-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A specified list of actual global functions descends as an initial parameter list.
Source: Stacks, More on Algebra, Tag 06LN, using 07QM; Algebra, Tags 00KU and 00DV;
steps 5--6 of lem-trf-free-log-chart-ordinary-parameters.
(blueprint: lem-trf-strict-local-parameter-descent).

Proof: choose a Noetherian affine neighbourhood of w. Its ordinary local ring B
is Noetherian by localization. The affine strict-local comparison identifies the
recorded ring A with B's algebraic strict henselization and, by its base-map equation,
identifies the two germs of every specified function. The hypothesis gives a list
of dim A generators of m_A, so its cotangent classes form a basis, by the regular
local cotangent-dimension criterion and the dimension bound by the embedding dimension.
In particular A is regular, and the strict-henselization regularity equivalence makes
B regular. The canonical cotangent base-change isomorphism sends each specified class
tensored with 1 to its given class in A. Independence of their classes in A therefore
descends along the faithful residue-field extension. Extend the independent classes
in B to a basis and lift the additional vectors to m_B. Nakayama says the combined
list generates m_B. Its length is the cotangent dimension, hence dim B by regularity.
It is the required parameter list, with the original values in their original order.
An empty specified list simply extends by a full system; the argument includes fields. -/
theorem strictLocal_parameters_descent
    (W : Scheme.{u}) [IsLocallyNoetherian W]
    (w : W) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ W) (ht : (Scheme.SpecToEquivOfField Ω W t).1 = w)
    (a : List Γ(W, ⊤))
    (ha : ∃ (_ : IsLocalRing (Scheme.strictHenselizationRing t))
        (_ : IsNoetherianRing (Scheme.strictHenselizationRing t)),
      ∃ b : List (Scheme.strictHenselizationRing t),
        IsLocalRing.IsRegularSystemOfParameters
          (a.map (fun f ↦ (strictLocalRingStrictHenselizationIso W t).hom
            (strictLocalGerm W t (Scheme.Etale.mk (𝟙 W))
              (CategoryTheory.Over.homMk t (by simp)) f)) ++ b)) :
    ∃ b : List (W.presheaf.stalk w),
        IsLocalRing.IsRegularSystemOfParameters
          (a.map (fun f ↦ W.presheaf.germ ⊤ w (by trivial) f) ++ b) := by sorry

end AlgebraicGeometry
