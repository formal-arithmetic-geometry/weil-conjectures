/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.ScalarPullbackStrictConeData

/-! # A step of strict scalar pullback cone naturality -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The generator and two-coordinate normalizations force scalar composition and units.
Source: Stacks, sites-modules.tex, Tag 03EK and derived.tex, Tag 014E;
Step 10 of strict scalar pullback cone naturality.
(blueprint: lem-sf-scalar-pullback-strict-coherence).

Proof: the ordinary scalar associator sends (p tensor s) tensor z to
p tensor (j(s) z), and its inverse sends p tensor z to (p tensor 1) tensor z.
The completed coefficient inclusions compose because their composites have the same
residues at every finite level, and limit projections jointly detect equality.
Tensor balancing, restriction and sheafification prove these are inverse natural
chain maps, with the asserted association formula. Quotient inclusions compose.
On the iterated local generator, successive level maps therefore have final
multiplier iota_EF(b) pi_F(j(s)) pi_F(z), whereas the direct map has multiplier
iota_EF(b) pi_F(j(s) z); these agree by multiplicativity of pi_F. Sheaf tensor
and inverse-image generator extensionality prove the level equality. The
product comparisons respect association, since every projection is the tensor
of the same projection followed by scalar multiplication. Applying the two
cone-coordinate formulas and the strict diagonal Roos-map formulas reduces
each coordinate of the cone equality to the level equality. The coordinates
jointly determine a cone map. With the identity extension the quotient map
is the identity and the formula is multiplication by the residue of s;
this is precisely the published tensor multiplication unitor. The same two
coordinate calculation gives the cone unit equality. Only level and cone
fields of the data are used; no property of a derived transformation is
assumed in this chain-level calculation. -/
theorem scalarPullbackStrictCoherence {X Y : AlgebraicGeometry.Scheme.{t}}
    (g : X ⟶ Y) :
    (∀ D : ScalarPullbackStrictConeData l E L ι g,
      ScalarPullbackCompositionFormula l E L ι g D) ∧
    (∀ D : ScalarPullbackStrictConeData l E E (AlgHom.id ℚ_[l] E) g,
      ScalarPullbackUnitFormula l E g D) := by sorry

end WeilConjectures
