/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizedOrdinaryPullbackData

/-! # Normalized scalar-localization comparison for one pullback

Source: Stacks Project, Tags 03EL, 0D6D and 07A4; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-per-localized-ordinary-edge).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.LocalizedOrdinary

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (ϖ : PbcIntegralRing l E)

/-- Scalar localization commutes with one ordinary ringed pullback, with the
coefficient-unit, tensor-generator, inverse-unit and derived-model normalizations.
Source: Stacks Project, Tags 03EL, 0D6D, 07A4, 06YS and 0G7E;
Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-per-localized-ordinary-edge).

Proof: the completed coefficient map carries the constant section ϖ to ϖ.
Use the unit-preserving inverse-image/localization comparison to view the
inverse image of B_X[1/ϖ] as the localization of the inverse-image ring.
The localization universal property extends c_g uniquely to the coefficient map.
Its restriction to B_X is precisely c_g followed by iota_Y.

Flatten both ordinary functors to R_Y tensor over g⁻¹B_X with g⁻¹M.
The first flattening sends e tensor (b tensor m) to e iota_Y(b) tensor m;
the second sends e tensor (e₀ tensor m) to e c_g^E(e₀) tensor m.
The coefficient-unit equation proves balancing. The inverses insert 1, and
multiplication proves both inverse identities. The localization module
comparison identifies the pulled fraction coordinates. These formulas commute
with restrictions and are natural in M, so sheafification gives the ordinary
natural isomorphism, its unit formula, its tensor formula and inverse formula.

Take flat-term K-flat resolutions. Inverse image and scalar extension preserve
this resolving class, so all functors are computed by the preceding ordinary
maps. Apply them degreewise; they commute with differentials. Localize the
resolving category to obtain the derived isomorphism. By construction its
comparison with the fixed computation counits is the stated derived_model
equation. Naturality extends across inverted quasi-isomorphisms. The argument
works for any ϖ, including nilpotent ϖ and the zero localization, and uses no
invertibility of c_g or boundedness of the input complex. -/
theorem localizedOrdinaryEdge_exists {X Y : Scheme.{u}} (g : Y ⟶ X) :
    Nonempty (Edge l E ϖ g) := by sorry

end AlgebraicGeometry.Scheme.LocalizedOrdinary
