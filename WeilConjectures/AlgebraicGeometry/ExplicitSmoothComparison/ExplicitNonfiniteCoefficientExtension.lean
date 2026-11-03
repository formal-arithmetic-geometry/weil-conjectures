/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ExplicitCoefficientAssembly

/-! # Nonfinite coefficient extension of explicit adjunctions

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-purity-transport/sk-prop-sp-comparison-brown-explicit.proof.md.
(blueprint: lem-pur-explicit-nonfinite-coefficient-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace AlgebraicGeometry.ProEtale.ExplicitSmoothComparison

/-- Reconstruct the nonfinite adjunctions from a coherent normalized finite
family, with the counit equations whose source or target coefficient is nonfinite.
The finite-to-finite equations are not part of this conclusion.

Source: integral and rational/closure paragraphs, and transported normalization
in sk-prop-sp-comparison-brown-explicit.proof.md.
(blueprint: lem-pur-explicit-nonfinite-coefficient-extension).

Proof in words. Apply the integral Hom-bijection construction to the supplied
finite adjunctions at the distinguished quotient rings. Their scalar equations
supply the compatible transition units and counits. The integers and rationals
constructors are the bottom finite-extension cases, with their canonical scalar
identifications retained. The normalized derived-limit
comparison identifies this tower adjunction with the literal condensed integral
operations. Transport through the integral purity isomorphism; the reductions of
its counit are exactly the supplied finite counits, with their specified scalar
and root-line maps. Localize the natural integral Hom bijections to each finite
extension of Q_ell. The scalar Hom comparisons and the compact-support/source
comparisons identify the resulting adjunction with the literal rational
operations, independently of lattices. For the algebraic closure, descend each
finite collection of objects and morphisms to a common finite extension and
apply the model-independent filtered-colimit Hom bijection. The units and
counits descend from these same bijections. The coefficient comparison counit
identities prove the mixed scalar equations for reduction, localization, field
extension and inclusion into the algebraic closure. A continuous map from an
integral coefficient ring to a finite ring factors through a finite quotient;
combine integral reduction compatibility with the given finite scalar equation.
Transitivity and transport through the specified coefficient isomorphisms handle
listed composites and changes of presentation. In each step retain the specified
maps and their counit
identities, rather than choosing unrelated adjunctions. If the field is not
algebraically closed, the geometric comparisons are obtained after conservative
algebraic-closure base change and descend with their dualizing and Tate-line
comparisons. Only the nonfinite adjunctions are supplied by this construction;
the assembled finite entries are definitionally the input finite family. -/
theorem explicitNonfiniteCoefficientExtension (k : Type u) [Field k]
    (ell : ℕ) [Fact ell.Prime] (hchar : (ringChar k).Prime)
    (hne : ell ≠ ringChar k) (a : FiniteFamily ell k)
    (hn : a.normalized ell k) (ha : a.affineNormalized ell k)
    (hs : a.scalarCompatible ell k) :
    ∃ r : NonfiniteFamily ell k, MixedScalarCompatible ell k (assemble a r) := by
  sorry

end AlgebraicGeometry.ProEtale.ExplicitSmoothComparison
