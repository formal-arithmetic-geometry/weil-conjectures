/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.CompactSupportNativeSystemEvaluation

/-! Comparison of the recorded and native compact-support towers, before total limit. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- Compare the whole recorded reduction tower with native proper/open reduction.

Source: the coherent tower construction in blueprint order 1494, first sentence;
Bhatt--Scholze, Definition 6.7.6; Stacks Tags 06YY, 0941 and 0A95.
(blueprint: lem-qcqs-compact-support-native-tower-comparison).

Proof: compute reduction on a flat-term K-flat representative. The reduction models
of SX and of the calculus used for the recorded coherent tower are the localization
of the same ordinary quotient tensor functor. Its universal derived counit gives a
natural comparison preserving every quotient map and finite evaluation. Apply exact
open extension and then the separately right-derived proper image on the sequence
site, and restrict scalars to the completed ring. This gives an isomorphism of whole
derived strict towers. The recorded coherent tower is obtained by these same operations;
the universal comparison of resolutions identifies their realizations before evaluation.
On each quotient the map is precisely the inverse SX evaluation followed by the
recorded evaluation. Thus the displayed equation follows from the normalization of
those universal comparisons. Quasi-isomorphism invariance descends the comparison
and its inverse to all derived inputs. This argument uses the entire strict diagrams,
not faithfulness of evaluation in a derived category. For zero input and empty opens
it is the same localization comparison of zero complexes. No total limit or recorded
integral compact-support functor occurs in this statement. -/
theorem qcqsCompactSupport_nativeTowerComparison
    (SX : CoefficientDerivedSystemCalculus l E X) :
    let hT := exists_compactSupportReductionTower l E K₀ X Y f hl c
    let T := hT.choose_spec.choose_spec.2.2.choose
    let eT := hT.choose_spec.choose_spec.2.2.choose_spec.2.choose_spec.2.choose
    let N := SX.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g
    let e (n : ℕ) :=
      Functor.isoWhiskerLeft SX.reduction (compactSupportSystemEvaluation l E c n) ≪≫
        Functor.isoWhiskerRight (SX.reductionEvaluation n)
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    ∃ α : T ≅ N ⋙ coefficientSequenceDerivedRestriction l E Y,
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (coefficientConstantTowerEvaluation l E Y n).map (α.hom.app K) ≫
            (coefficientRestrictedEvaluationIso l E Y n).hom.app (N.obj K) ≫
            (coefficientFiniteDerivedRestriction l E Y n).map ((e n).hom.app K) =
          (eT n).hom.app K := by
  sorry

end WeilConjectures
