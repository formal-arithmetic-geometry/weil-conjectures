/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization

/-!
# Intrinsic affine sections and the generic stalk of a monoscheme

Source: ILO VIII 3.1.4(i), 3.1.9 and 3.2.4, pp.98--103
(blueprint: lem-trf-monoscheme-generic-chart-completion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Monoscheme

/-- The generic stalk is a group, and the intrinsic section monoid of an affine chart
is fine and has this stalk's group completion as its canonical completion.
Source: ILO VIII 3.1.4(i), 3.1.9 and 3.2.4, pp.98--103
(blueprint: lem-trf-monoscheme-generic-chart-completion).

Proof: transport the chart sheaf isomorphism to its global sections. The canonical
numerator-section map P → Γ(Spec_mon P, M) is an isomorphism: the closed point has
smallest neighbourhood the entire spectrum, and its localization at the unit face is
P. Thus intrinsic chart sections are fine. The generic point of this chart is the
empty prime, whose smallest neighbourhood is D(a), where a is the product of a finite
generating family. In the face localization at a, each generator is invertible:
the product of the other generators divided by a is its inverse. This localization
is P^gp. Sections on a smallest neighbourhood equal the stalk, since that neighbourhood
is terminal in the opposite neighbourhood category. The germ therefore induces an
isomorphism from the group completion of the chart sections to the generic stalk.
The completion of this group stalk is itself: its inverse sends a quotient to the
product of its numerator and its denominator's inverse. Compose these identifications
to obtain the displayed equivalence. Its formula on generators is the defining germ
formula for degree. All constructions use the canonical sheaf restrictions, so they
are independent of the chosen chart presentation. The empty monoscheme has no C;
a rank-zero chart and an empty generating family give the trivial group. -/
theorem generic_chart_completion (M : Fine.{u})
    (C : ToricComponent M) :
    (∃ e : FineFan.stalk M.space.presheaf C.genericPoint ≃* C.lattice,
      e.toMonoidHom = Algebra.GrothendieckGroup.of) ∧
    ∀ U : ComponentAffineOpens C,
      FineFan.IsFine (M.space.presheaf.obj (op U.1.1)) ∧
      ∃ e : Algebra.GrothendieckGroup (M.space.presheaf.obj (op U.1.1)) ≃* C.lattice,
        ∀ p, e (Algebra.GrothendieckGroup.of p) = degree C U p := by
  sorry

end AlgebraicGeometry.Monoscheme
