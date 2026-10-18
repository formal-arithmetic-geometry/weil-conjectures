/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit

/-!
# Epimorphic towers on the pro-etale site

Source: the Weil conjectures blueprint, main-20261015, `sec-proetale-coefficients`,
`sk-prop-pe-milnor`, lemma `det-pe-milnor-epimorphic`
(blueprint: det-pe-milnor-epimorphic).

## Main declarations

* `milnorLimitProjection`: the tuple of the limit projections, in degree zero.
* `milnorLimitComparison_condition`: its zero-null-homotopy condition.
* `milnorLimitComparison`: the canonical map to the recorded Roos complex.
* `milnor_epimorphic`: all three conclusions for an epimorphic tower.

The derived limit is exactly `WeilConjectures.integralOperationsRoos`, as in
`AlgebraicGeometry.Scheme.ProEt.milnor_sequence`, not a new cone construction.
-/

@[expose] public section

set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe v u t w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The tuple of the ordinary limit projections, embedded in degree zero.

Source: the Weil conjectures blueprint, main-20261015, `sk-prop-pe-milnor`,
`det-pe-milnor-epimorphic` (blueprint: det-pe-milnor-epimorphic). -/
noncomputable def milnorLimitProjection
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableProducts C]
    (M : ℕᵒᵖ ⥤ C) [HasLimit M] :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (limit M) ⟶
      ∏ᶜ (fun n : ℕ ↦ (Scheme.ProEt.milnorSingleTower M).obj (op n)) :=
  Pi.lift (fun n : ℕ ↦
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (limit.π M (op n)))

/-- The tuple of limit projections admits the zero null-homotopy for `1 - T`.

Source: the Weil conjectures blueprint, main-20261015, `sk-prop-pe-milnor`,
`det-pe-milnor-epimorphic` (blueprint: det-pe-milnor-epimorphic).

Proof: compose with the nth product projection. The composite with `1 - T` is
`p_n - p_(n+1) t_n = 0` by the limit cone equation, after applying the additive
single-complex functor. Product extensionality gives zero. The differential of
the zero cochain is zero, giving the displayed cocycle condition. -/
theorem milnorLimitComparison_condition
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableProducts C]
    (M : ℕᵒᵖ ⥤ C) [HasLimit M] :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (limit M))
          (∏ᶜ (fun n : ℕ ↦ (Scheme.ProEt.milnorSingleTower M).obj (op n))) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (milnorLimitProjection M ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ (Scheme.ProEt.milnorSingleTower M).obj (op n))
            (WeilConjectures.integralOperationsTowerStep (Scheme.ProEt.milnorSingleTower M))) =
      0 := by
  sorry

/-- The canonical map from the ordinary limit in degree zero to `Cone(1 - T)[-1]`.
The target is the exact Roos model used by the recorded Milnor sequence. The lift
uses the tuple of actual limit projections and the zero null-homotopy.

Source: the Weil conjectures blueprint, main-20261015, `sk-prop-pe-milnor`,
`det-pe-milnor-epimorphic` (blueprint: det-pe-milnor-epimorphic). -/
noncomputable def milnorLimitComparison
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableProducts C]
    (M : ℕᵒᵖ ⥤ C) [HasLimit M] :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (limit M) ⟶
      WeilConjectures.integralOperationsRoos (Scheme.ProEt.milnorSingleTower M) :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ (Scheme.ProEt.milnorSingleTower M).obj (op n))
      (WeilConjectures.integralOperationsTowerStep (Scheme.ProEt.milnorSingleTower M)))
    (milnorLimitProjection M) 0 (milnorLimitComparison_condition M)

/-- Epimorphic transitions imply that `1 - T` is epic, the first derived limit
vanishes, and the canonical ordinary-to-derived-limit map is an isomorphism.

Source: the Weil conjectures blueprint, main-20261015, `sk-prop-pe-milnor`,
`det-pe-milnor-epimorphic` (blueprint: det-pe-milnor-epimorphic).

Proof:
1. Evaluation at an affine weakly contractible object W preserves cokernels and
zero by det-pe-sections-limits-colimits. Thus every epimorphic transition becomes
a surjection of R(W)-modules. Products are computed sectionwise by the same node.
2. Given (a_n), choose right inverses s_n to these surjections. Set m_0 = 0 and
m_(n+1) = s_n(m_n - a_n). Then (1 - T)m = a on W.
3. Apply det-pe-sections-conservative to P -> P -> 0, using the preceding
surjectivity, to conclude that 1 - T is an epimorphism of module sheaves.
4. Clause 2 of det-pe-milnor-sequence identifies H^0 of its recorded Roos complex
with the ordinary inverse limit (def-pur-sheaf-inverse-limit), H^1 with the
cokernel of 1 - T, and every other H^p with zero. Hence H^1 vanishes.
5. The comparison is the inclusion of this kernel into the two-term Roos complex,
with zero second component. The differential of Cone(1 - T)[-1] is -(1 - T);
negating degree 1 identifies it with the usual two-term complex. The comparison
induces the degree-zero kernel identification and is a quasi-isomorphism. The
localization def-weil-abstract-derived-category makes it an isomorphism.
The argument uses arbitrary ring sheaves (def-weil-sheaf-of-modules-category),
and includes the zero tower and the empty scheme. -/
theorem milnor_epimorphic
    (X : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)]
    (M : ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R)
    (ht : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
      (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op)) ∧
      IsZero ((WeilConjectures.integralOperationsRoos
        (Scheme.ProEt.milnorSingleTower M)).homology 1) ∧
      IsIso (DerivedCategory.Q.{w}.map (milnorLimitComparison M)) := by
  sorry

end AlgebraicGeometry.ProEtale
