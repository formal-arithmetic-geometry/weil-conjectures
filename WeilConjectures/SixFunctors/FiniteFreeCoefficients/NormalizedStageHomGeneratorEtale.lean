/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration

/-! Generator case for the normalized ordinary-etale stage Hom comparison.

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- The normalized stage Hom comparison is invertible on each flat-model generator.

Proof: identify the normalized tensorator with the canonical etale tensor comparison, transpose
along the etale tensor-Hom adjunction, and use the locally-closed lisse-projective generator
calculation. The generator comparison word has invertible factors: finite projective evaluation,
open and closed exceptional projection, and the ordinary coefficient direct-image comparison.
The transpose uniqueness equation then identifies that word with the displayed `Sites.homMap`.
This statement isolates the generator calculation from the thick-generation argument.
(blueprint: lem-sf-normalized-stage-hom-generator-etale).
-/
theorem normalized_stage_hom_generator_etale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsNoetherian X]
    {s t : Stage l E} (a : Arrow s t)
    (μ : Sites.TensorComparison false a.ringMap X)
    (hμ : Sites.NormalizedTensor false a.ringMap X μ)
    (M : Sites.D false s.ring X) (hM : Sites.Ctf false s.ring X M)
    (T : Sites.D false s.ring X)
    (hT : ∃ (S : Scheme.{u}) (j : S ⟶ X) (hj : IsImmersion j)
      (L : Sheaf S.smallEtaleTopology (ModuleCat s.ring)),
      FlatModelEtaleLisseProjective s.ring L ∧
        Nonempty (T ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension s.ring j hj).obj L))) :
    IsIso (Sites.homMap false a.ringMap X μ T M) := by
  sorry

end WeilConjectures.FiniteFreeCoefficients
