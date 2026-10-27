/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.PurSequenceAdjointResolutionData
import Sheaf.Paper.PurSequenceOrdinaryFactorization
import Sheaf.Paper.PurSequenceDerivedNormalization

/-! # The normalized whole-system Hom correspondence for the sequence projection

Source: blueprint `sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`,
coefficient-comparison paragraph; Stacks 03D7, 0940, 06YY, 09T5, 0D6E and 070I.
(blueprint: lem-pur-sequence-projection-hom-normalization).

The existing resolution-data record includes the geometric projection, its ringed
factorization, ordinary tensor/limit transposes, universal derived comparisons,
and identification of both units and counits. The additional equations below
specify the full derived Hom correspondence and its simultaneous-resolution formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceRestriction coefficientSequenceEvaluation
  coefficientFiniteDerivedExtension scalarReductionExtension
  coefficientConstantTowerLimit coefficientSequenceLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

set_option linter.unusedVariables false in
/-- The sequence projection identifies the supplied coefficient adjunction on whole
system Hom sets, with the ordinary tensor transpose followed by the actual limit
of every simultaneous K-injective replacement.
Source: blueprint coefficient-comparison paragraph of `fix-prop-coherence.proof.md`;
Stacks 03D7, 0940, 06YY, 09T5, 0D6E and 070I
(blueprint: lem-pur-sequence-projection-hom-normalization).

Proof, following the seven steps of the node:
1. Apply lem-pur-sequence-site-completion-projection to the actual quotient tower.
The constant-system geometric inverse image and quotient structural map define p.
Insert the constant completed ring to obtain the ringed factorization g after a.
The unchanged module sections and transitions identify a_* with exact restriction
U and g_* with limit, as in def-coef-ringed-sequence-site.
2. Use lem-coef-sequence-projection-derived-adjunction for ordinary tensor/limit
adjoints. A map h gives b tensor x mapped to b times pi_n(h(x)); conversely f gives
x mapped to (f_n(x tensor 1))_n. Balancing is A-linearity and transition compatibility
is quotient semilinearity. These inverse sheaf-module correspondences are natural.
3. By lem-pc-kflat-resolution and lem-weil-pbc-ringed-topoi-derived-pullback, derive
on flat-term K-flat representatives. Their one strict quotient tensor complex is
the model in lem-coef-derived-system-evaluation-calculus, fixing alpha before evaluation.
4. Use prop-pur-kinjective-resolutions-exist and the composition comparison of
lem-weil-pbc-ringed-topoi-derived-pushforward-composition. Exactness of U identifies
Ra_* with D(U). For every K-injective I and replacement j:UI to J, kappa is the
class of lim(j), which is a quasi-isomorphism. UI need not be K-injective.
5. Apply lem-sfb-resolving-derived-adjunction-normalization: the derived transpose
of the localized f after epsilon is the localized ordinary transpose followed by eta.
The composition normalization of step 4 gives exactly adj_0(f) followed by lim(j),
with the ordinary module-limit identification inserted in the displayed Lean equation.
6. K-flat resolutions and lem-weil-pbc-kinjective-hom-derived cover every full derived
Hom set by homotopy classes of system chain maps. The universal comparisons and
fraction-extension Hom bijection give naturality and independence of all choices.
7. By lem-coef-sequence-pushforward-limit-projections and the supplied calculus,
transport this adjunction along alpha and kappa. This gives the first displayed
whole-Hom equation. Identity transposes give precisely the supplied unit and counit,
as recorded in the resolution data. No faithfulness of evaluation is assumed. -/
theorem purSequenceProjectionHomNormalization
    (F : FiniteFieldDatum.{t}) (hl : l ≠ F.p)
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S) :
    ∃ D : PurSequenceResolutionData l E W S,
      (∀ (P : DerivedCategory (scalarReductionSource l E W))
        (N : coefficientSequenceDerived l E W) (v : S.reduction.obj P ⟶ N),
        S.adjunction.homEquiv P N v =
          D.derived.adjunction.homEquiv P N (D.derived.left.hom.app P ≫ v) ≫
            D.derived.right.hom.app N) ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients
          (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
          Q)
        (flatQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
          (Q.X i))
        (I : CochainComplex (coefficientSequenceModules l E W) ℤ) [I.IsKInjective]
        (f : (D.ordinary.pullback.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I)
        (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
        (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
        [QuasiIso j],
        S.adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
            (D.derived.left.inv.app (DerivedCategory.Q.obj Q) ≫
              D.derived.ε.app Q ≫ DerivedCategory.Q.map f) ≫
            (D.derived.model I J j).hom =
          DerivedCategory.Q.map
              ((D.ordinary.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex D.ordinary.limit (.up ℤ)).hom.app I) ≫
            DerivedCategory.Q.map
              (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
                scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map j)) := by
  classical
  obtain ⟨O, ⟨H⟩⟩ := purSequenceOrdinaryFactorization l E W
  obtain ⟨A⟩ := purSequenceDerivedNormalization l E W F hl S hS O H
  let D : PurSequenceResolutionData l E W S := ⟨O, H, A⟩
  have hom_formula (P : DerivedCategory (scalarReductionSource l E W))
      (N : coefficientSequenceDerived l E W) (v : S.reduction.obj P ⟶ N) :
      S.adjunction.homEquiv P N v =
        D.derived.adjunction.homEquiv P N (D.derived.left.hom.app P ≫ v) ≫
          D.derived.right.hom.app N := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_comp, ← D.derived.unit P]
    have hn := D.derived.right.hom.naturality v
    simp only [Category.assoc]
    rw [← hn]
  refine ⟨D, hom_formula, ?_⟩
  intro Q hQ flatQ I hI f J hJ j hj
  rw [hom_formula]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [D.derived.hom_normalization]
  simp only [Category.assoc]
  rw [(D.derived.composition_model I J j).2]

end WeilConjectures
