/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomGeneratorEtale
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomThickReductionEtale
import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomScalarTensorNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomThickLocus
import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration

/-! Normalized internal-Hom stage comparison on the ordinary etale site. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem stage_hom_transpose
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : Sites.D false A X)
    (v : Etale.EtaleHomLeft X φ M ⟶ Etale.EtaleHomRight X φ M)
    (hv : Etale.IsEtaleHomTranspose X φ M v) (K : Sites.D false A X)
    (μ : Sites.TensorComparison false φ X)
    (hμ : Sites.NormalizedTensor false φ X μ) :
    Sites.homMap false φ X μ K M = v.app (op K) := by
  cases hμ
  have htrans : v.app (op K) =
      Etale.CoefficientPairingChange.evaluationComparison φ X K M := by
    apply ((Etale.derivedTensorHomAdjunction (ModuleCat B)
    ((Etale.scalarExtension φ X).obj K)).homEquiv _ _).symm.injective
    exact (hv K).symm.trans (Equiv.symm_apply_apply _ _).symm
  dsimp only [Sites.homMap, Sites.scalar, Sites.hom, Sites.adj, Sites.tensor]
  rw [WeilConjectures.finiteHom_scalar_tensor_normalization]
  exact htrans.symm

/-- Ordinary etale finite-stage internal-Hom comparison on ctf objects.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
(blueprint: lem-sf-normalized-stage-hom-isomorphism-etale).

Proof: Obtain the generic etale evaluation-transpose comparison and its thick isomorphism locus.
The normalized tensorator identifies its transpose with `Sites.homMap`. For a fixed ctf second
input, define the locus of first inputs on which this transpose is invertible. The generator
helper proves the locus contains every flat-model generator, and finite-ring flat-constructible
thick generation places the ctf first input in their triangulated envelope. The thick-reduction
helper applies the zero, shift, triangle and retract closure data from the generic comparison.
The resulting invertibility statement, transported through the transpose identity, is the claimed
`Sites.homMap` isomorphism. -/
theorem normalized_stage_hom_isomorphism_etale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    {s t : Stage l E} (a : Arrow s t)
    (μ : Sites.TensorComparison false a.ringMap X)
    (hμ : Sites.NormalizedTensor false a.ringMap X μ)
    (K M : Sites.D false s.ring X)
    (hK : Sites.Ctf false s.ring X K) (hM : Sites.Ctf false s.ring X M) :
    IsIso (Sites.homMap false a.ringMap X μ K M) := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  let : IsNoetherian X := {}
  obtain ⟨v, hv, _⟩ := Etale.etaleHomComparison_thickLocus X a.ringMap
  let Q : ObjectProperty (Sites.D false s.ring X)ᵒᵖ :=
    fun T ↦ IsIso ((v M).app T)
  let G : ObjectProperty (Sites.D false s.ring X) := fun T ↦
    ∃ (S : Scheme.{u}) (j : S ⟶ X) (hj : IsImmersion j)
      (L : Sheaf S.smallEtaleTopology (ModuleCat s.ring)),
      FlatModelEtaleLisseProjective s.ring L ∧
        Nonempty (T ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension s.ring j hj).obj L))
  have hg : G ≤ Q.unop := by
    intro T hT
    change IsIso ((v M).app (op T))
    rw [← stage_hom_transpose X a.ringMap M (v M) (hv M).1 T μ hμ]
    exact normalized_stage_hom_generator_etale D l hl E X a μ hμ M hM T hT
  have hgen := congrFun (etale_flatConstructible_thickGeneration X s.ring) K
  have hmem : ObjectProperty.triangEnvelope G K := by
    change ObjectProperty.triangEnvelope (fun T ↦
      ∃ (S : Scheme.{u}) (j : S ⟶ X) (hj : IsImmersion j)
        (L : Sheaf S.smallEtaleTopology (ModuleCat s.ring)),
        FlatModelEtaleLisseProjective s.ring L ∧
          Nonempty (T ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
            ((flatModelEtaleExtension s.ring j hj).obj L))) K
    exact Eq.mp hgen ⟨hK.1.1, hK.1.2, hK.2⟩
  have hQ : Q (op K) :=
    normalized_stage_hom_thick_reduction_etale X Q
      (hv M).2.2.1 (hv M).2.2.2.2.1
      (hv M).2.2.2.2.2.1 (hv M).2.2.2.2.2.2 G hg hmem
  have he := stage_hom_transpose X a.ringMap M (v M) (hv M).1 K μ hμ
  rw [he]
  exact hQ

end WeilConjectures.FiniteFreeCoefficients
