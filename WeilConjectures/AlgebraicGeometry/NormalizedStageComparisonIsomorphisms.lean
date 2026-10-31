/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedStageComparisonObligations
import WeilConjectures.AlgebraicGeometry.NormalizedStageTensorSymmetryData
import WeilConjectures.AlgebraicGeometry.NormalizedStageGeometricIsomorphismData
import WeilConjectures.AlgebraicGeometry.NormalizedStageSiteIsomorphismData
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
import all WeilConjectures.SixFunctors.ClosedOpenDualizingMate

/-! # Invertibility of the normalized finite-stage comparisons

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- Pointwise isomorphisms of the prescribed stage maps and the site bridges.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--2;
the finite quotient direct-image, closed-shriek, dualizing, Hom and Verdier comparisons.
(blueprint: lem-sf-normalized-stage-comparison-isomorphisms).

Proof: obtain the normalized scalar tensorators and the canonical Koszul symmetries from the
sitewise derived tensor construction. Apply the geometric comparison theorem to the normalized
tensorators. For the site record, use the generic finite-ring compact-support comparison at the
specified dualizing input. The base Spec D.k is Noetherian. The schemes X and Z are Noetherian by
finite type and quasi-compactness over D.k. For the closed immersion, identify the stipulated direct
coefficient map with the hom of closedScalarIso using their common scalar-pullback mate. This proves
that site field on every input. Apply the stage Hom-site theorem for the final site field. Collect
the site record and the geometric record with the normalized tensor and symmetry witnesses. -/
theorem normalized_stage_comparison_isomorphisms
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T X Z : Scheme.{u})
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k))) :
    ∃ (μ : ∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t),
        Sites.TensorComparison pro a.ringMap X)
      (σ : ∀ (pro : Bool) (s : Stage l E),
        Sites.tensor pro s.ring X ≅ (Sites.tensor pro s.ring X).flip),
      (∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t),
        Sites.NormalizedTensor pro a.ringMap X (μ pro a)) ∧
      (∀ (pro : Bool) (s : Stage l E),
        Sites.NormalizedSymmetry pro s.ring X (σ pro s)) ∧
      (∀ pro : Bool, Sites.StageComparisonIsomorphisms pro l E f i c (μ pro)) ∧
      (letI := c.hasCompactification
       Sites.StageComparisonSiteIsomorphisms l E f i c) := by
  obtain ⟨μ, σ, hμ, hσ⟩ := normalized_stage_tensor_symmetry_data l E X
  have hi := normalized_stage_geometric_isomorphism_data
    D l hl E T X Z f i c μ hμ
  have hhom := normalized_stage_site_isomorphism_data D l hl E X
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : IsNoetherian X := {}
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of D.k))
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of D.k))
  have : IsNoetherian Z := {}
  let := c.hasCompactification
  have hsi : Sites.StageComparisonSiteIsomorphisms l E f i c := by
    refine ⟨?_, ?_, hhom⟩
    · intro s t a
      exact Etale.ExceptionalCoefficients.compactSupport_isIso a.ringMap
        (HasCompactification.compactification (X ↘ Spec (.of D.k))) (omega s.ring c)
    · intro s t a M _
      have hc (N : Cat s.ring Z) :
          Etale.finiteCoefficientDirectImageMap a.ringMap i N =
            (Etale.closedScalarIso a.ringMap i).hom.app N := by
        rw [Etale.closedScalarIso_hom_app, Etale.finiteCoefficientDirectImageMap_eq_mate]
        rfl
      rw [hc]
      infer_instance
  exact ⟨μ, σ, hμ, hσ, hi, hsi⟩

end WeilConjectures.FiniteFreeCoefficients
