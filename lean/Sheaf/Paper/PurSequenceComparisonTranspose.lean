/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S6
-/
module

public import Sheaf.Paper.PurSequenceKFlatComparisonShifts
public import Sheaf.Paper.SequenceKInjectiveComparisonShifts

/-! # Transposes under the two normalized coefficient comparisons

Source: Stacks Project, Tags 06YY, 09T5 and 0D6E
(blueprint: lem-pur-sequence-comparison-transpose).
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

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The common strict K-flat model and the normalized K-injective comparison
intertwine the specified coefficient adjunction with the ordinary transpose.
Source: Stacks 09T5, 070I and 0D6E; blueprint coefficient-comparison paragraph
(blueprint: lem-pur-sequence-comparison-transpose).

Proof: use flat-term K-flat resolutions for the first variable and K-injective
resolutions for the second. The normalized left comparison uses the strict
ordinary pullback, including its quotient transitions. The normalized right
comparison uses the constant-ring factorization and is represented by the
ordinary limit of a simultaneous replacement. The resolving-class derived
adjunction therefore sends a chain map to its ordinary transpose followed by
this right comparison. The specified coefficient adjunction is the canonical
transport of this adjunction to the same reduction and total-limit functors.
The universal comparison squares identify their full fraction-extension Hom
bijections, so the displayed identity holds for arbitrary Q and I, not only
resolving objects. Pre- and postcomposition and inversion of quasi-isomorphisms
preserve it. This argument compares system morphisms before evaluation and
uses no faithfulness claim for evaluation. -/
theorem purSequenceComparisonTranspose
    (F : FiniteFieldDatum.{t}) (hl : l ≠ F.p)
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (H : PurSequenceRingedFactorization l E W O)
    (RP : coefficientSequenceDerived l E W ⥤
      DerivedCategory (scalarReductionSource l E W))
    (η : (SequenceKInjectiveComparison.push l E W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RP)
    (κ : RP ≅ coefficientSequenceLimit l E W)
    (hn : SequenceKInjectiveComparison.Normalization l E W RP η κ) :
    ∃ A : PurSequenceKFlatComparison l E W S O,
    ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (f : (O.pullback.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
    S.adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
      (A.reductionCounit.app Q ≫ DerivedCategory.Q.map f) =
    DerivedCategory.Q.map ((O.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex O.limit (.up ℤ)).hom.app I) ≫
      η.app I ≫ κ.hom.app (DerivedCategory.Q.obj I) := by sorry

end WeilConjectures
