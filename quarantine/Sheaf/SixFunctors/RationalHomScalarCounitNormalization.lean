/-
Copyright (c) 2026 The SHEAF contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalOperationsData
public import Sheaf.SixFunctors.RationalHomAdjunction
public import Sheaf.Paper.CompletedTensorHomTranspose

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

/-- The closed evaluation map associated with a permitted rational Hom pair.
Source: the normalized tensor-Hom counit used in the finite scalar evaluation argument
(blueprint: lem-sf-rational-hom-scalar-evaluation). -/
def normalizedCounit
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (K M : sfRationalConstructibleCategory l E X) :
    (RationalVerdier.tensor D l hl X E).obj
        (K, (homRight l E X h K).obj M) ⟶ M :=
  (@pullbackTensorRationalBraiding l _ E _ _ _ X
      (RationalVerdier.units D l hl X) K ((homRight l E X h K).obj M)).hom ≫
    (@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).evaluation
      ⟨(op K, M), h K M⟩

/-- The supplied Hom identification has the normalized closed counit on every rational
object. This is the rational extension of its integral evaluation field.
Source: finite scalar evaluation argument, normalization and localization paragraphs
(blueprint: lem-sf-rational-hom-scalar-evaluation). -/
theorem homIdentification_counit_normalized
    (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w)
    (h : HomIdentification l E X D hl w A) :
    ∀ K M : sfRationalConstructibleCategory l E X,
      (h.adjunction K).counit.app M = normalizedCounit D l hl X E h.permitted K M := by
  sorry


end WeilConjectures.RationalOperations
