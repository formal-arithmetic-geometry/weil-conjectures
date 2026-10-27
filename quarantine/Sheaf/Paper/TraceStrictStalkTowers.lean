/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q52 and K9
-/
module

public import Sheaf.Paper.TraceStalkCompositorTowerData

/-! # Finite germ maps on whole coefficient-system complexes

Source: Stacks Tags 0F4F and 05V1 and the strict-diagram part of blueprint
Local powers (b) (blueprint: lem-trf-strict-stalk-towers).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical finite germ maps assemble on the actual strict coefficient systems.
No derived realization or integral comparison is chosen in this result.
Source: Stacks sites.tex, Tags 0F4F and 05V1; the parent proof, Steps 2, 3, 6 and 8
(blueprint: lem-trf-strict-stalk-towers).

Proof: identify evaluation of the sequence inverse image with finite inverse image
by the mate of the sectionwise direct-image evaluation square. Its unit equation
is the finiteUnit equation. Restrict scalars along the quotient maps and take the
canonical finite pullback-stalk comparison in each degree. Both a differential and
an actual quotient transition change only the section in a germ, so their squares
commute, giving c as an isomorphism of whole towers, natural in the complex.
The initial identity-point neighbourhood computes sections and gives gamma. Define
e by gamma after pullback followed by c. Apply the finite composition equation to
(v,id) for finiteSections and to (h,f,w) for finiteComposition; all maps preserve
the actual quotient transitions. The inverse-image unit gives finiteIdentity.
Reindex pointed neighbourhoods by Spec(alpha), leaving their sections unchanged.
Its inverse is reindexing by alpha inverse. This defines r and commutes with the
same differentials and transitions. Both routes in reparamSquare send a pullback
germ to the germ with lift pr_V theta u Spec(alpha), proving the strict square.
These arguments also apply to exponent one, the zero complex, and identity maps. -/
theorem trfStrictStalkTowers (D : FiniteFieldDatum.{u}) :
    ∃ T : TrfStrictStalkTowerData l E D, TrfStrictStalkTowerCoherent l E D T := by
  sorry

end WeilConjectures
