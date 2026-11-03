/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.LocalizedTopChernStatementModels

/-!
# The geometric laws of a natural frame-normalized Kummer family

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-localized-top-chern.proof.md`, Steps 1, 2, comparison, and Step 4
(blueprint: lem-pur-localized-chern-kummer-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Any natural family with the positive Kummer frame formula satisfies the signed
forget-support equation, the negative Cartier normalization, and the transverse
sum formula. This is a comparison theorem for an arbitrary given family; it does
not construct or choose a family.

Source: `thm-pur-localized-top-chern.proof.md`, Steps 1, 2, comparison with the
flag class, and Step 4 (blueprint: lem-pur-localized-chern-kummer-laws).

Proof:
1. Evaluate the given family on a bundle's tautological section. Its frame
formula specifies the coordinate orientation on every trivializing open of the
total space. Affine zero-section purity and bottom supported gluing show that
these local values uniquely determine this universal class. Naturality then
identifies the class at every regular section with the pullback of that class.
2. In rank one this universal class is the positive Kummer boundary. The
relative Cartier construction has the opposite local boundary by
`lem-pur-divisor-class`. Compare the universally normalized zero-section classes
and pull back along the section. The zero ideal is invertible because the
single local equation of a regular section is a nonzerodivisor. The canonical
site and Tate comparisons give exactly minus `canonicalCartierSupportedMap`,
with the displayed `geoCartierEtaleClass`, not an arbitrary Cartier witness.
3. Pull back the universal class to the complete flag bundle. Its locally
split filtration gives an iterated product of the localized line classes.
On adapted frames this is the same positive Kummer coordinate product; frame
independence and bottom gluing on the universal total space identify them.
Pull back along the section to identify the corresponding flag class.
4. Forget support. Supported cup functoriality identifies the forgotten flag
class with the product of the negative first Chern classes of the line
quotients. `lem-pur-chern-flag-formula` identifies this with (-1)^r c_r(F).
The full-support case of `lem-pur-flag-pullback-injective` descends this equality
to the base. These are the canonical ordinary Chern coordinates already used
by `localizedChernOrdinary`; the rank-zero empty product is c_0=1.
5. For a transverse sum pull back to the product of the two complete flag
bundles. Its pullback is injective by applying flag injectivity twice. On the
universal sum bundle, bottom gluing identifies its orientation with the cup
product of the two orientations: the coordinate lists concatenate, the twists
multiply in that order, and even degrees give no sign. Supported cup
functoriality and `lem-pur-kunneth-supported` give the same equality after
pulling back by the two sections. Use their scheme-theoretic intersection and
the canonical comparison with the sum zero scheme, then descend by the two
split injections. Transversality supplies regularity of the sum section. Empty
support and rank-zero cases follow from the zero arrow and the cup unit.
-/
theorem localizedTopChernKummerFamily_laws (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) (hbase : P.LocalizedTopChernBaseChange c)
    (hframe : P.LocalizedTopChernStatementFrameFormula c) :
    P.LocalizedTopChernStatementForgetSupport c ∧
      P.LocalizedTopChernStatementLine c ∧ P.LocalizedTopChernDirectSum c := by
  sorry

end WeilConjectures.PurityFiniteSetting
