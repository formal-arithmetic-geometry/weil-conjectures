/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion

import Sheaf.Paper.SupportedRationalLatticeGeneration

/-! # Supported finite-model rigidity from integral to rational coefficients

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md (2), closed-fibre comparison obligation.
Agent-formulated conditional transfer; exact full-generality reference WANTED.
(blueprint: lem-sfb-supported-rational-model-rigidity-transfer).

The quantified integral premise and rational conclusion use every path in every finite
qcqs open-closed tree. Every admissible support chain is such a path after adjoining
complementary siblings; paths may stop at any vertex. Root paths include the identity
chain. No condition is imposed on the open complement of the fixed closed immersion.
The coefficient pairs are identified as ring objects, retaining the full continuous-map
condensed rings. The symbols R and K below denote those condensed rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Integral supported finite-model comparison implies rational supported finite-model
comparison for the same torsion-cohomologically rigid closed pair. No lattice on the
rational model is part of the hypotheses, and transition maps are unrestricted.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), first paragraph;
agent-formulated conditional transfer, exact full-generality reference WANTED.
(blueprint: lem-sfb-supported-rational-model-rigidity-transfer).

Proof: The geometric generation theorem chooses the coefficient localization and
expresses each supported rational model as a finite iterated extension of scalar
extensions of supported integral finite models. For each generator, apply hR on
its integral support path, then the individual coefficient-localization theorem.
Transport the resulting isomorphism across the generator's derived isomorphism.
The proved closed-restriction derived-operations theorem supplies a morphism of
distinguished triangles whose components are the actual restriction maps. The
triangle isomorphism theorem makes the comparison property closed under
extensions. Induction on the finite extension product proves comparison for the
rational model. The torsion hypothesis is retained but this conditional transfer
does not use it. The two independent geometric and localization arguments are
stated in the imported modules, with their sources and full proofs in words. -/
theorem supported_rational_model_rigidity_transfer
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R K : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj K] [IsCommMonObj K]
    (hRK :
      (Nonempty (Mon.mk R ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∧
        Nonempty (Mon.mk K ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ]))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk R ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)) ∧
        Nonempty (Mon.mk K ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    {T₀ T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace T₀] [QuasiSeparatedSpace T₀]
    (t : T₀ ⟶ T) [IsClosedImmersion t]
    (ht : ∀ (F : Sheaf T.smallEtaleTopology Ab.{u + 1}),
      Scheme.IsTorsionAbelianSheaf F → ∀ q : ℕ,
        Function.Bijective (Etale.cohomologyMap t F q))
    (hR : ∀ (S : Scheme.{u}) (tree : QcqsOpenClosedTree T) (p : tree.Path S)
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj R S)),
      HasFiniteConstantLocalModel R S L →
      IsIso ((Functor.rightDerivedPullback (upperStar R t)
      ((Functor.whiskerRight (upperStarLowerStarAdjunction R t).unit
          (condensedModuleSections R T) ≫
        Functor.whiskerLeft (upperStar R t)
          (Functor.whiskerLeft (Mod.forget (condensedRingObj R T₀))
            ((sheafSections (Scheme.ProEt.topology T₀) Ab.{u + 1}).map
              (MorphismProperty.Over.homMk
                (pullback.lift t (𝟙 T₀)
                  ((Category.comp_id t).trans (Category.id_comp t).symm))
                (pullback.lift_snd _ _ _)).op))) :
        condensedModuleSections R T ⟶ upperStar R t ⋙ condensedModuleSections R T₀)).app
      ((DerivedCategory.singleFunctor _ 0).obj ((p.extension R).obj L)))) :
    ∀ (S : Scheme.{u}) (tree : QcqsOpenClosedTree T) (p : tree.Path S)
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj K S)),
      HasFiniteConstantLocalModel K S L →
      IsIso ((Functor.rightDerivedPullback (upperStar K t)
      ((Functor.whiskerRight (upperStarLowerStarAdjunction K t).unit
          (condensedModuleSections K T) ≫
        Functor.whiskerLeft (upperStar K t)
          (Functor.whiskerLeft (Mod.forget (condensedRingObj K T₀))
            ((sheafSections (Scheme.ProEt.topology T₀) Ab.{u + 1}).map
              (MorphismProperty.Over.homMk
                (pullback.lift t (𝟙 T₀)
                  ((Category.comp_id t).trans (Category.id_comp t).symm))
                (pullback.lift_snd _ _ _)).op))) :
        condensedModuleSections K T ⟶ upperStar K t ⋙ condensedModuleSections K T₀)).app
      ((DerivedCategory.singleFunctor _ 0).obj ((p.extension K).obj L))) := by
  have _torsionRigidity := ht
  obtain ⟨a, ha, hgen⟩ := supported_rational_lattice_generation ℓ R K hRK T
  have hops := closed_restriction_derived_operations K t
  have := hops.2.2.1
  have := hops.2.2.2.1
  have := hops.2.2.2.2.1
  let P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj K T))) :=
    fun M ↦ IsIso ((closedRestrictionRho K t).app M)
  have hbase : IsLocalizedSupportedModel a T ≤ P := by
    rintro M ⟨S, tree, p, H, hH, ⟨e⟩⟩
    have hi := supported_coefficient_localization ℓ a ha t ((p.extension R).obj H)
      (hR S tree p H hH)
    exact (NatTrans.isIso_app_iff_of_iso (closedRestrictionRho K t) e).mpr hi
  have hclosed : ∀ (Δ : Triangle _) (_ : Δ ∈ distTriang _),
      P Δ.obj₁ → P Δ.obj₃ → P Δ.obj₂ := by
    intro Δ hΔ h₁ h₃
    obtain ⟨r, hr₁, hr₂, hr₃⟩ := hops.2.2.2.2.2.2.1 Δ hΔ
    change IsIso ((closedRestrictionRho K t).app Δ.obj₂)
    rw [← hr₂]
    change IsIso ((closedRestrictionRho K t).app Δ.obj₁) at h₁
    change IsIso ((closedRestrictionRho K t).app Δ.obj₃) at h₃
    rw [← hr₁] at h₁
    rw [← hr₃] at h₃
    exact CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃ r
      ((closedRestrictionPhi K T).map_distinguished _ hΔ)
      ((closedRestrictionPsi K t).map_distinguished _ hΔ) h₁ h₃
  have hiter (n : ℕ) : (IsLocalizedSupportedModel a T).extensionProductIter n ≤ P := by
    induction n with
    | zero => exact hbase
    | succ n ih =>
      rw [ObjectProperty.extensionProductIter_succ]
      rintro M ⟨A, B, f, g, δ, hΔ, hA, hB⟩
      exact hclosed (Triangle.mk f g δ) hΔ (hbase A hA) (ih B hB)
  intro S tree p L hL
  obtain ⟨n, hn⟩ := hgen S tree p L hL
  exact hiter n _ hn

end AlgebraicGeometry.ProEtale.CondensedRing
