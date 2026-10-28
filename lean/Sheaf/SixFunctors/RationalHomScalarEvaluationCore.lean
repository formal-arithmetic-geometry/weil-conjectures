/-
Copyright (c) 2026 The SHEAF contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalHomScalarCounitNormalization

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Closed transpose transports normalized counits through the rational tensor and Hom
scalar comparisons. This is the categorical core of finite scalar evaluation.
Source: finite scalar evaluation argument, transpose paragraph
(blueprint: lem-sf-rational-hom-scalar-evaluation). -/
theorem scalarEvaluation_of_normalizedCounits
    (hE : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (hL : ∀ K M : sfRationalConstructibleCategory l L X,
      constructibleRationalHomPairs l L X (op K, M))
    (eE : ∀ K M : sfRationalConstructibleCategory l E X,
      (RationalVerdier.tensor D l hl X E).obj
          (K, (homRight l E X hE K).obj M) ⟶ M)
    (eL : ∀ K M : sfRationalConstructibleCategory l L X,
      (RationalVerdier.tensor D l hl X L).obj
          (K, (homRight l L X hL K).obj M) ⟶ M)
    (heE : ∀ K M, eE K M = normalizedCounit D l hl X E hE K M)
    (heL : ∀ K M, eL K M = normalizedCounit D l hl X L hL K M) :
    ∀ K M : sfRationalConstructibleCategory l E X,
      (RationalVerdier.tensor D l hl X L).map
          (Prod.mkHom (𝟙 ((RationalVerdier.scalar l X E L ι).obj K))
            (rationalHomScalarComparison l E L ι X
              ⟨(op K, M), hE K M⟩).hom) ≫ eL
          ((RationalVerdier.scalar l X E L ι).obj K)
          ((RationalVerdier.scalar l X E L ι).obj M) =
        (@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ ι X
          (RationalVerdier.units D l hl X)).inv.app
            (K, (homRight l E X hE K).obj M) ≫
          (RationalVerdier.scalar l X E L ι).map (eE K M) := by
  sorry


end WeilConjectures.RationalOperations
