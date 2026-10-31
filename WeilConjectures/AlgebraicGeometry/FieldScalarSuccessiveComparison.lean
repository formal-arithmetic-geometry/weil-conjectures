/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldScalarNormalizedData

/-! # Successive field-scalar comparison

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, paragraph (1).
(blueprint: lem-sp-field-scalar-successive-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale.FieldScalar

/-- Three normalized scalar data admit their tensor compositor and reduction square.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, paragraph (1).
(blueprint: lem-sp-field-scalar-successive-comparison).

Proof:
The quotient maps for the composite field inclusion equal the composites of the
quotient maps: check this on the surjective quotient maps from O_E. Joint monicity of
completed projections gives the same equality for the completed ring maps. The ordinary
tensor associator sends t tensor (s tensor x) to (image(s) times t) tensor x, with inverse
inserting one. Tensor balancing proves the inverse equations and naturality. Use this
at every level, transported through the three level isomorphisms of ExactExtension.
The transition formulas show these level maps commute with every quotient transition,
so they define the ordinary whole-system compositor with the displayed generator law.
Exact extension sends quasi-isomorphisms to quasi-isomorphisms. Its invertible counits
therefore descend this compositor and give its representative equation. For integral
scalar extension, scalar associativity on flat-term K-flat complexes gives the derived
compositor and its counit equation by the universal left-derived property. Finally,
on the same flat K-flat complex both routes around the reduction square multiply the
same three factors. The ideal-quotient tower associator proves equality already on
strict tower complexes, through the actual normalized quotient maps. The representative
equations for the three reduction comparisons, and strict tensor descent, descend this
equality to all derived objects and roofs. Bases need not be compatible across fields. -/
theorem field_scalar_successive_comparison {l : ℕ} [Fact l.Prime] {E F L : Type u}
    [Field E] [Field F] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    [FiniteDimensional (Padic l) L]
    {ι : E →ₐ[Padic l] F} {κ : F →ₐ[Padic l] L} {T : Scheme.{u}}
    {DA : SpCoefficientTowersAbelian.{u, u} l E T}
    {DB : SpCoefficientTowersAbelian.{u, u} l F T}
    {DC : SpCoefficientTowersAbelian.{u, u} l L T}
    {RA : SpReductionTower l E T DA} {RB : SpReductionTower l F T DB}
    {RC : SpReductionTower l L T DC}
    (D₁ : ScalarData l E F ι T DA DB RA RB)
    (D₂ : ScalarData l F L κ T DB DC RB RC)
    (D₃ : ScalarData l E L (κ.comp ι) T DA DC RA RC) :
    Nonempty (Successive D₁ D₂ D₃) := by sorry

end AlgebraicGeometry.ProEtale.FieldScalar
