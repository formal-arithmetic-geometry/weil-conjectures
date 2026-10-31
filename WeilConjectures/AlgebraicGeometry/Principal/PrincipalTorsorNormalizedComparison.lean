/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
/-! Independent comparison result for the principal torsor sign calculation. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale
/-- The open adjunction and the closed-support resolution comparison admit the normalization
on every cocycle used in the sign calculation.
Source: Stacks Tags 03AJ, 0A45, 06XR; the normalization step of the principal-torsor node.
Proof: use extension-by-zero adjunction and the integer generator for openSection. Apply
Hom(Q,-) to the integral localization sequence in an injective resolution; injectivity makes
it degreewise exact. Identify Hom(Z_T,I) with global sections and use the closed-cone lift,
a quasi-isomorphism, to obtain the relative comparison. The Ext resolution equivalence and
the two projections of the closed-cone lift give the representative (zp(1),0). The counit
triangle takes the open inclusion to one. Use the derived supported-section realization
for the support component.
(blueprint: lem-pur-principal-torsor-normalized-comparison). -/
theorem principalTorsorNormalizedComparison :
    ∃ C : PrincipalTorsorComparisons.{u}, C.Normalized := by sorry
end AlgebraicGeometry.Etale
