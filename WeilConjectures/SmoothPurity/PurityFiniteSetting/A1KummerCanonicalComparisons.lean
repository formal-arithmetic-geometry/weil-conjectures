/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.A1KummerSiteTransport

/-! # Canonical comparisons for the affine-line Kummer calculation
Source: det-prop-a1-kummer.proof.md, site comparisons and Base change on Y.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The geometric and site comparisons preserve the specified units, Kummer class and
edge section. This contains no assertion about the cohomology being free or vanishing,
and no assertion that an exchange is invertible.
Source: det-prop-a1-kummer.proof.md, site comparisons and Base change on Y
(blueprint: new-pur-a1-kummer-canonical-comparisons).

Proof: identify the polynomial and Laurent pullback families with Line and Punctured,
over the base. The affine-line isomorphism and its projection and coordinate
normalizations are proved in a1KummerLineFamilyIso_normalization. The Laurent-family
isomorphism and its unit normalization are proved in
a1KummerPuncturedFamilyIso_normalization. These identifications preserve coordinateUnit.
Compare finite root
coefficients by the normalized roots/pure-tensor pullback isomorphisms. A primitive
root gives the degree-zero coefficient comparison; it is used only for computation.
For each affine projection use exact etale/pro-etale inverse image and its canonical
right-direct-image counit mate. The constructed kummerSiteCohomologyIso applies
cohomology and the total/Plus compatibility isomorphisms to this actual mate.
Combine it with the preceding geometry and coefficient identifications to obtain e.
For b=false, apply direct image to the inverse primitive-root constant-to-root map
on Line; this changes the root coefficient to the actual untwisted constant.
For b=true, retain the root tensor and use its normalized transport along the
Laurent-family isomorphism. Take j to be exact comparison of the primitive-root
constant-to-root map on Y.
The proved kummerSiteComparison_unit gives the bounded-below unit identity.
Identify its coefficient and single/total comparisons to obtain both unit equations.
The ordinary module-class bijection identifies the normalized coordinate class with
frameKummerEtale_hom_eq_normalized. Exact site comparison therefore gives the actual
pro-etale frameKummer. The proved kummerSiteComparison_adjunct supplies naturality
of adjoint transposition. The shift comparisons and H0 then give the displayed generator
equation, rather than an unspecified basis.
For horizontal pullback, frameKummerEtale_hom_pullback proves the actual etale
frame-class square from Kummer-boundary and root-insertion naturality. Transport this
square through exact site comparison, retaining its single and shift comparisons,
to obtain the pro-etale class equation. Pasting the coefficient pullback squares
gives both coefficient squares. The proved generic mate calculation yields
both unit equations, including their degree-zero cohomology consequences. Finally
transpose the class equation through the two adjunctions; shift compatibility of
the exchange mate and the H0/shift comparison gives the degree-one generator equation.
The exchange calculation is made directly for the specified pro-etale mate, using
its adjunction and shift structure. No general comparison of exchanges or
spectral-object edge theorem is needed. All projections are affine, hence qcqs,
and the comparison on these finite coefficient
sheaves is valid over arbitrary bases. No finite-type assumption is imposed on g. -/
theorem a1Kummer_canonical_comparisons (P : PurityFiniteSetting.{u}) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    (∀ (Y : Scheme.{u}) (a : Y ⟶ Spec (.of P.field.k)),
      P.A1KummerSiteTransport ζ hζ a) ∧
    (∀ (Y' Y : Scheme.{u}) (g : Y' ⟶ Y) (a : Y ⟶ Spec (.of P.field.k)),
      P.A1KummerExchangeNormalization g a) := by sorry

end WeilConjectures.PurityFiniteSetting
