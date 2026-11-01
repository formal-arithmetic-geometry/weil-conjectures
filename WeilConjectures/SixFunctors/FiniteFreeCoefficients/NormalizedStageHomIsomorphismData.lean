/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomIsomorphismEtale
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomIsomorphismProEtale

/-! Internal-Hom stage comparison on ctf pairs.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- The normalized scalar internal-Hom transpose is invertible on ctf pairs on either site.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
(blueprint: lem-sf-normalized-stage-hom-isomorphism-data).

Proof: Split on the Boolean site flag. The false case is the ordinary etale theorem;
the true case is the pro-etale theorem. Each branch receives the original coefficient arrow,
normalized tensorator and ctf inputs. -/
theorem normalized_stage_hom_isomorphism_data
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (pro : Bool) {s t : Stage l E} (a : Arrow s t)
    (μ : Sites.TensorComparison pro a.ringMap X)
    (hμ : Sites.NormalizedTensor pro a.ringMap X μ)
    (K M : Sites.D pro s.ring X)
    (hK : Sites.Ctf pro s.ring X K) (hM : Sites.Ctf pro s.ring X M) :
    IsIso (Sites.homMap pro a.ringMap X μ K M) := by
  cases pro
  · exact normalized_stage_hom_isomorphism_etale D l hl E X a μ hμ K M hK hM
  · exact normalized_stage_hom_isomorphism_proetale D l hl E X a μ hμ K M hK hM

end WeilConjectures.FiniteFreeCoefficients
