/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogGroupAction

/-!
# Very tame actions on fs log schemes

Source: ILO, Exposé VI 3.1, printed p.73
(blueprint: def-per-very-tame-fs-log-action).

Triviality on a geometric stalk is tested on all pointed relative étale diagrams.
Every germ has such a representative. Associated log germs have the same image
in the characteristic monoid, which is the quotient by units.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Very tameness means tame geometric inertia, trivial characteristic action, and
trivial action on the strict local log stratum. The latter two conditions are written
on section representatives of the actual geometric stalks. The equality of lifts
identifies the geometric points in the relative étale diagram. The ring difference
condition says exactly that pullback on the stratum quotient ring is the identity.
Source: ILO VI 3.1 (i)--(iii), printed p.73
(blueprint: def-per-very-tame-fs-log-action). -/
def FSLogGroupAction.IsVeryTame {G : Type v} [Group G]
    {X : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction G X) : Prop :=
  a.IsTame ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
      (g : G), t ≫ (a.baseAction g).hom = t →
      ∀ (W V : X.scheme.Etale) (k : V.left ⟶ W.left)
        (hk : k ≫ W.hom = V.hom ≫ (a.logMap g).base)
        (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (z : (Scheme.pointSmallEtale t).fiber.obj V), z.left ≫ k = w.left →
        (∀ s : X.logStructure.monoidSheaf.obj.obj (op W),
          Associated
            (X.logStructure.toEtalePrelogStructure.germ t V z
              ((a.logMap g).sectionMap W V k hk s))
            (X.logStructure.toEtalePrelogStructure.germ t W w s)) ∧
        ∀ r : Γ(W.left, ⊤),
          strictLocalGerm X.scheme t V z (k.appTop r) -
            strictLocalGerm X.scheme t W w r ∈ X.logStructure.nonunitIdeal t

end AlgebraicGeometry
