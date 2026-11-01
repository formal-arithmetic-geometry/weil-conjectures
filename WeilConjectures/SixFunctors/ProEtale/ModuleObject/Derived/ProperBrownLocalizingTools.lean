/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLocalizingPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingBrownRepresentability

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
/-- Proper pushforward and coproduct part of the general-field localizing tools.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
sk-thm-purity-transport.proof.md, Steps 2--4

Proof plan: establish proper preservation on finite constant-model generators using the
proper higher-image finiteness theorem, then use finite truncation dévissage and the
characteristic-free heart coproduct criterion. Apply localizing minimality to obtain the
proper restriction and coproducts. Finally use structural Brown hypotheses, essential
smallness and the set-generated derived Brown theorem to represent every homological
functor in the target closure.
(blueprint: lem-dla1-general-field-proper-brown-tools). -/
theorem properBrownLocalizingTools (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [PerfectField k] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {T S : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))]
    [S.Over (Spec (CommRingCat.of k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k))]
    [IsSeparated (S ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k))]
    (p : T ⟶ S) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p] :
    (∀ K, localizingClosureProEtale Λ T K → localizingClosureProEtale Λ S
      ((moduleObjectDerivedPushforward Λ p).obj K)) ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((localizingClosureProEtale Λ T).ι ⋙ moduleObjectDerivedPushforward Λ p)) ∧
    ∀ (H : (localizingClosureProEtale Λ S).FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      BrownRepresentableOnLocalizingClosure Λ S H := by
  have hp := properLocalizingPreservation (ℓ := ℓ) (k := k) Λ hΛ p
  exact ⟨hp.1, hp.2, localizingBrownRepresentability (ℓ := ℓ) (k := k) Λ hΛ⟩

end AlgebraicGeometry.ProEtale.CondensedRing
