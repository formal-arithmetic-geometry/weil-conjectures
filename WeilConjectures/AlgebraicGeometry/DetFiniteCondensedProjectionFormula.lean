/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOpenShriekComparison
import WeilConjectures.AlgebraicGeometry.CanonicalFiniteCoefficientPullTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived

/-!
# Finite-coefficient condensed projection formula

Source: the latest blueprint,
`sec-six-functors-basics/sk-thm-sf-pf-adic/det-thm-sf-pf-finite.md`, node
det-thm-sf-pf-finite, order 2765; proof in the latest blueprint's
`det-thm-sf-pf-finite.proof.md` (blueprint: det-thm-sf-pf-finite).

This is the condensed-module projection-formula statement attached to
`det-thm-sf-pf-finite`.  The ordinary condensed-module `PF` of `det-def-sf-exchanges` is
the `CompactificationReindexing.pf` component `Rp_*(γ) ∘ π`.  Étale complexes are
transported by the canonical site comparison `ν^*` and by the canonical finite
coefficient equivalence whose scalar map is `constRingSheafToCondensedRingObj`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Keep the native derived-structure calculations sequential to control peak memory.
set_option Elab.async false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj

section DerivedSquare

universe a b c d

variable {A : Type a} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type b} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  {C : Type c} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type d} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F₁ : A ⥤ B) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₁.PreservesFlat] [F₁.IsLeftAdjoint] [F₁.Monoidal]
  (F₂ : B ⥤ D) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint] [F₂.Monoidal]
  (G₁ : A ⥤ C) [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₁.PreservesFlat] [G₁.IsLeftAdjoint] [G₁.Monoidal]
  (G₂ : C ⥤ D) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [G₂.PreservesFlat] [G₂.IsLeftAdjoint] [G₂.Monoidal]
  (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) [NatTrans.IsMonoidal τ.hom]

end DerivedSquare


namespace AlgebraicGeometry.ProEtale

/-- Bounded constructibility supplies the lower bound needed to use the canonical
`siteComparisonDerivedPullbackPlus` functor.
Proof: the second clause of `isBoundedConstructible` gives `a ≤ b` with
`H^i K = 0` for `i ∉ [a, b]`; in particular `H^i K = 0` for `i < a`, so `K` lies in
`D^{≥ a}` by `DerivedCategory.isGE_iff`, hence in the `plus` part of the standard
t-structure.
Source: blueprint node det-thm-sf-pf-finite, order 2765, proof step "Naturality and
bounded-below target" (bounded `K` is bounded below) (blueprint: det-thm-sf-pf-finite). -/
theorem boundedConstructible_plus
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (K : AlgebraicGeometry.Etale.DerivedCategoryModule Λ X)
    (hK : AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible Λ X K) :
    DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, b, _, hv⟩ := hK.2
  exact ⟨a, (_root_.DerivedCategory.isGE_iff K a).2
    (fun q hq ↦ hv q (Or.inl hq))⟩

-- Keeping the component condition folded avoids expanding concrete derived structures
-- while specializing the generic projection-formula lemmas.
private def properProjectionIsIso
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] [UpperStarPreservesFlat B]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) B))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B)) : Prop :=
  IsIso (((rightDerivedLowerStarProjectionMap B g).app K).app L)

private theorem ordinary_proper_factor_of_full_pf
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] [UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B))
    (h : HasProjectionFormulaOfCompactification B c K L) :
    properProjectionIsIso B c.g
      ((openImmersionLowerShriek B c.i).mapDerivedCategory.obj K) L := by
  unfold properProjectionIsIso
  rw [HasProjectionFormulaOfCompactification, projectionMapOfCompactification_app_app] at h
  simpa only [isIso_comp_right_iff] using h

private theorem properProjectionIsIso_of_iso
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] [UpperStarPreservesFlat B]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) B)}
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B)}
    (eK : K ≅ K') (eL : L ≅ L') (h : properProjectionIsIso B g K L) :
    properProjectionIsIso B g K' L' := by
  unfold properProjectionIsIso at h ⊢
  have := h
  exact NatTrans.isIso_app_app_of_iso (rightDerivedLowerStarProjectionMap B g) eK eL

attribute [local instance 20000] sheafBraidedCategory
attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
attribute [local irreducible] Mod.monoidalCategoryStruct Mod.monoidalCategory Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit Functor.mapDerivedCategory
  DerivedCategory.Qh Functor.leftDerivedFunctorCompNatIso
  Functor.leftDerivedFunctorIsoMapDerivedCategory Functor.mapDerivedCategoryCompIso
  CondensedRing.leftDerivedUpperStarTensor leftDerivedUpperStarTensorComparison
  Functor.leftDerivedTensorComparison

set_option maxHeartbeats 0 in
-- The native derived tensor structures require substantial kernel reduction.
private theorem canonical_finite_projection_isIso_iff
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y))) :
    IsIso (CondensedRing.moduleObjectProjectionMap (Profinite.continuousMapRingObj A) p K L) ↔
      properProjectionIsIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) p
        ((finiteCoefficientDerivedEquivalence X A).functor.obj K)
        ((finiteCoefficientDerivedEquivalence Y A).functor.obj L) := by
  unfold properProjectionIsIso
  obtain ⟨mX, hX, _⟩ := canonicalFiniteCoefficientTensor A X
  obtain ⟨mY, hY, _⟩ := canonicalFiniteCoefficientTensor A Y
  let := mX
  let := mY
  let NX := (finiteCoefficientModEquivalence X A).functor
  let NY := (finiteCoefficientModEquivalence Y A).functor
  let F := CondensedRing.upperStar (Profinite.continuousMapRingObj A) p
  let G := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p
  have : F.PreservesFlat := CondensedRing.preservesFlat_upperStar _ p
  have : NX.PreservesFlat := Functor.preservesFlat_of_isEquivalence NX
  have : NY.PreservesFlat := Functor.preservesFlat_of_isEquivalence NY
  let τ : NY ⋙ G ≅ F ⋙ NX := (upperStarFiniteCoefficientModEquivalenceIso p A).symm
  have : NatTrans.IsMonoidal τ.hom := by
    have := canonicalFiniteCoefficientPullTensor A p mX mY hX hY
    dsimp only [τ, Iso.symm_hom]
    infer_instance
  let α := Functor.leftDerivedFunctorCompNatIso F NX NY G τ
  let d : NX.leftDerivedFunctor ≅ (finiteCoefficientDerivedEquivalence X A).functor :=
    NX.leftDerivedFunctorIsoMapDerivedCategory
  let c : NY.leftDerivedFunctor ≅ (finiteCoefficientDerivedEquivalence Y A).functor :=
    NY.leftDerivedFunctorIsoMapDerivedCategory
  let tx := asIso NX.leftDerivedTensorComparison
  let ty := asIso NY.leftDerivedTensorComparison
  have h : Adjunction.ComparisonCompatible α F.leftDerivedTensorComparison
      G.leftDerivedTensorComparison tx ty := derivedComparisonCompatible F NX NY G τ
  have hn := comparisonCompatible_congr α
    (CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison _ p).symm
    (leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).symm h
  have ht := comparisonCompatible_transport α c d
    (CondensedRing.leftDerivedUpperStarTensor (Profinite.continuousMapRingObj A) p)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} A)) p)
    tx ty hn
  let adj := CondensedRing.derivedUpperStarLowerStarAdjunction
    (Profinite.continuousMapRingObj A) p
  let adj' := ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) p
  let α' := Functor.isoWhiskerRight c.symm G.leftDerivedFunctor ≪≫ α ≪≫
    Functor.isoWhiskerLeft F.leftDerivedFunctor d
  let m_C := tensorTransport _ _ d tx
  let m_D := tensorTransport _ _ c ty
  have H : Adjunction.ComparisonCompatible α'
      (CondensedRing.leftDerivedUpperStarTensor (Profinite.continuousMapRingObj A) p)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} A)) p)
      m_C m_D := ht
  have hβ (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))) :
      IsIso ((mateEquiv adj adj' α'.hom).app N) :=
    Adjunction.isIso_mateEquiv_app_of_isIso adj adj' α'
      (finiteCoefficientDerivedEquivalence Y A).toAdjunction
      (finiteCoefficientDerivedEquivalence X A).toAdjunction N
  have := hβ K
  have := hβ (((CondensedRing.derivedTensor (Profinite.continuousMapRingObj A) X).obj K).obj
    (F.leftDerivedFunctor.obj L))
  change IsIso (((adj.rightAdjointProjectionMap
      (CondensedRing.leftDerivedUpperStarTensor (Profinite.continuousMapRingObj A) p)).app
        K).app L) ↔ IsIso (((adj'.rightAdjointProjectionMap
          (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} A)) p)).app
            ((finiteCoefficientDerivedEquivalence X A).functor.obj K)).app
              ((finiteCoefficientDerivedEquivalence Y A).functor.obj L))
  constructor
  · intro h
    have := h
    exact Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv adj adj' H K L
  · intro h
    have := h
    have hs := Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv adj adj' H K L
    have : IsIso ((finiteCoefficientDerivedEquivalence Y A).functor.map
        (((adj.rightAdjointProjectionMap
          (CondensedRing.leftDerivedUpperStarTensor (Profinite.continuousMapRingObj A) p)).app
            K).app L) ≫
        (mateEquiv adj adj' α'.hom).app _ ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).rightDerivedFunctor.map
          ((m_C.hom.app K).app _ ≫
          ((ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).obj
            ((finiteCoefficientDerivedEquivalence X A).functor.obj K)).map
              (α'.inv.app L))) := by
      erw [hs]
      infer_instance
    have hmap : IsIso ((finiteCoefficientDerivedEquivalence Y A).functor.map
        (((adj.rightAdjointProjectionMap
          (CondensedRing.leftDerivedUpperStarTensor (Profinite.continuousMapRingObj A) p)).app
            K).app L)) := by
      simpa only [isIso_comp_right_iff] using this
    exact isIso_of_reflects_iso _ (finiteCoefficientDerivedEquivalence Y A).functor

private theorem ordinary_finite_projection_factor
    (A : Type) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) X)
    (L : Etale.DerivedCategoryModule (ULift.{u + 1} A) Y)
    (hK : _root_.DerivedCategory.TStructure.t.bounded K)
    (hLt : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} A) Y a b L) :
    properProjectionIsIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.g
      ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.i).mapDerivedCategory.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory.obj K))
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).mapDerivedCategory.obj L) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let M := (Etale.openImmersionLowerShriek B c.i).mapDerivedCategory.obj K
  have hM : _root_.DerivedCategory.TStructure.t.bounded M :=
    (Etale.openImmersionLowerShriek B c.i).bounded_mapDerivedCategory_obj hK
  obtain ⟨a, b, ht⟩ := hLt
  have hML := Etale.plus_derivedTensor_leftDerivedUpperStar c.g hM
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht)
  have : IsIso (((Etale.rightDerivedLowerStarProjectionMap B c.g).app M).app L) := by
    have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite (ULift.{u + 1} A) c.g
    infer_instance
  have hp := hasProjectionFormulaOfCompactification_of_comparison c
    (Iso.refl ((comparisonUpperStar B X).mapDerivedCategory.obj K))
    (Iso.refl ((comparisonUpperStar B Y).mapDerivedCategory.obj L)) hK hML
    (inferInstance : IsIso (((Etale.rightDerivedLowerStarProjectionMap B c.g).app M).app L))
  exact ordinary_proper_factor_of_full_pf B c
    ((comparisonUpperStar B X).mapDerivedCategory.obj K)
    ((comparisonUpperStar B Y).mapDerivedCategory.obj L) hp

set_option maxHeartbeats 0 in
-- Keep the supplied native derived structures while composing the three factors.
end AlgebraicGeometry.ProEtale
