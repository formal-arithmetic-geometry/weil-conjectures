/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralVerdier
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Models for integral duality under finite coefficient extension

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).

All comparisons below are fixed before invertibility is asserted. Finite dualizing
maps are counit transposes. Internal-Hom maps are evaluation transposes, and the
integral dualizing map is characterized by the coherent finite counit squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})

private theorem complete_iff_unrestricted (K : IntegralVerdier.Ambient l E X) :
    IsSfDerivedComplete l E X K ↔ IsDerivedCompleteUnrestricted l E X K := by
  constructor
  · intro hK
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hprime⟩
    let D : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hprime
        exponent_pos := by decide
        cardinality_eq := by simp
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl : l ≠ D.p := by change l ≠ p; omega
    exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E X D hl K).mp hK⟩
  · rintro ⟨D, hl, hK⟩
    exact (sfDerivedComplete_iff_legacy l E X D hl K).mpr hK

private theorem unrestricted_complete_of_iso
    {K M : IntegralVerdier.Ambient l E X} (e : K ≅ M)
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l E X M := by
  obtain ⟨D, hl, P, G, q, hq, a, hprod, δ, hδ⟩ := hK
  let := hprod
  refine ⟨D, hl, P, G, q, hq, a ≪≫ e, hprod,
    δ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ _
  refine Pretriangulated.Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · apply Pi.hom_ext
    intro n
    simp [Category.assoc]
  · simp
  · simp [Category.assoc, ← Functor.map_comp]

/-- The existing tensor presentation restricted to flat-term K-flat representatives.
Source: blueprint order 2494, tensor calculation
(blueprint: lem-coef-integral-finite-extension). -/
def tensorModel {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : IntegralHom.TensorPresentation.{u, u} X R) : ProEtaleTensorModel X R where
  tensor := a.tensor
  representative := Functor.isoWhiskerLeft
    (((IntegralHom.flat.{u, u} X R).lift (proEtaleFlatRepresentatives X R).ι
      (fun P ↦ P.property.1)).prod
      ((IntegralHom.flat.{u, u} X R).lift (proEtaleFlatRepresentatives X R).ι
        (fun P ↦ P.property.1))) a.representative

/-- The actual evaluation transpose for an arbitrary change of coefficient sheaves.
Source: blueprint order 2494, internal-Hom comparison
(blueprint: lem-coef-integral-finite-extension). -/
def homMap {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (a : IntegralHom.TensorPresentation.{u, u} X R)
    (b : IntegralHom.TensorPresentation.{u, u} X S)
    (K M : IntegralHom.Derived.{u, u} X R) :
    (pbcDerivedExtend φ).obj ((IntegralHom.hom.{u, u} X R).obj (op K, M)) ⟶
      (IntegralHom.hom.{u, u} X S).obj
        (op ((pbcDerivedExtend φ).obj K), (pbcDerivedExtend φ).obj M) :=
  (b.adjunction ((pbcDerivedExtend φ).obj K)).homEquiv _ _
    ((PurCompactSupport.scalarTensor φ (tensorModel X a) (tensorModel X b)).inv.app
        (K, (IntegralHom.hom.{u, u} X R).obj (op K, M)) ≫
      (pbcDerivedExtend φ).map ((a.adjunction K).counit.app M))

/-- Completeness in the intrinsic category makes the specified completion map invertible.
Source: blueprint order 2494, first paragraph
(blueprint: lem-coef-integral-finite-extension).
Proof: compare the intrinsic Roos completeness unit with the unrestricted one on a
flat-term K-flat resolution. Both have quotient components x ↦ 1 tensor x and zero
shifted coordinate. The finite-free completed-scalar comparison applies to this
same unit; hence its localized map is invertible. -/
theorem completion_isIso (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    IsIso ((completedScalarComparison l E L ι X).app K) := by
  exact ((finiteFreeCompletedScalarComparison l E L ι X).2.1 K
    ((complete_iff_unrestricted l E X K).mp hK)).1

/-- The fixed completion comparison on a complete input.
Source: blueprint order 2494 (blueprint: lem-coef-integral-finite-extension). -/
def completion (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K ≅
      (integralScalarExtensionOfUniverses l E L ι X).obj K :=
  letI := completion_isIso l E L ι X K hK
  asIso ((completedScalarComparison l E L ι X).app K)

/-- The canonical tensor/restriction identification of a finite reduction of T.
Source: blueprint order 2494, displayed quotient identification
(blueprint: lem-coef-integral-finite-extension). -/
def quotient (n : ℕ) (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (scalarReductionDerivedExtension l L X n).obj
        ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≅
      (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
        ((scalarReductionDerivedExtension l E X n).obj K) :=
  (scalarReductionDerivedExtension l L X n).mapIso (completion l E L ι X K hK).symm ≪≫
    (PurCompactSupport.finiteReductionIso l L X n).symm.app _ ≪≫
    (PurCompactSupport.tensorSquare (completedCoefficientMap l E L ι X)
      (integralScalarQuotientSheafMap l E L ι X n)
      (completedIntegralCommRingProjectionUnrestricted l E X n)
      (completedIntegralCommRingProjectionUnrestricted l L X n)
      ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec n)).app K ≪≫
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).mapIso
      ((PurCompactSupport.finiteReductionIso l E X n).app K)

/-- The canonical v: scalar-extended evaluation, transported through completion.
Source: blueprint order 2494, fourth paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def v (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) :
    (integralScalarExtensionOfUniverses l E L ι X).obj
        ((IntegralHom.hom.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M)) ⟶
      (IntegralHom.hom.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l L X)).obj
        (op ((integralScalarExtensionOfUniverses l E L ι X).obj K),
          (integralScalarExtensionOfUniverses l E L ι X).obj M) :=
  (completion l E L ι X _ (scalarInternalHom_complete l E X K M hM)).inv ≫
    homMap X (completedCoefficientMap l E L ι X) a b K M ≫
    (IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)).map
      (Prod.mkHom (completion l E L ι X K hK).inv.op
        (completion l E L ι X M hM).hom)

/-- Cross-field restriction commutes with the prescribed comparison-site realization.
Source: blueprint order 2494, finite counit comparisons
(blueprint: lem-coef-integral-finite-extension). -/
def finiteRealizationRestriction (n : ℕ) :
    finiteDualizingRealization l L X n ⋙
        pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n) ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)) ⋙
        finiteDualizingRealization l E X n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (finiteDualizingGenericDerivedRestriction X
      (integralScalarQuotientMap l E L ι n)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ProEtale.pbcDerivedComparisonRestrict X
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))) _ ≪≫
    Functor.associator _ _ _

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite cross-field dualizing map is the exceptional-adjunction transpose of
inverse compact-support comparison followed by extension of the counit and the unit.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def finiteEtaleU (n : ℕ) :
    (Etale.scalarExtension
      (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)) X).obj
        (finiteDualizingEtaleTerm l E D X n) ⟶ finiteDualizingEtaleTerm l L D X n :=
  (finiteDualizingEtaleAdjunction l L D X n).homEquiv _ _
    (Etale.ExceptionalCoefficients.comparisonInverse
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
        (finiteDualizingCompactification D X) (finiteDualizingEtaleTerm l E D X n) ≫
      (Etale.scalarExtension
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
        (Spec (.of D.k))).map (finiteDualizingEtaleCounit l E D X n) ≫
      (Etale.ExceptionalCoefficients.unitIso
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
        (Spec (.of D.k))).hom)

/-- Intrinsic finite u, transported by the scalar-unit-normalized realization square.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def finiteU (n : ℕ) :
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
        (integralDualizingFiniteTerm l E D X n) ⟶ integralDualizingFiniteTerm l L D X n :=
  ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n)).homEquiv
    _ _).symm
      ((finiteDualizingOrigin l E D X n).inv ≫
        (finiteDualizingRealization l E X n).map
          ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology
              (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)))).homEquiv
                _ _ (finiteEtaleU l E L ι X D n)) ≫
        (finiteRealizationRestriction l E L ι X n).inv.app
          (finiteDualizingEtaleTerm l L D X n) ≫
        (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n)).map
          (finiteDualizingOrigin l L D X n).hom)

/-- A presentation of the integral dualizing object with its coherent finite counits.
Coherence is essential: unrelated finite isomorphisms are not dualizing reduction data.
These are the reduction data provided by prop-coef-integral-dualizing.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension). -/
structure DualizingDatum (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] where
  omega : sfIntegralConstructibleCategory l F X
  reduction : ∀ n : ℕ,
    (scalarReductionDerivedExtension l F X n).obj omega.obj ≅
      integralDualizingFiniteTerm l F D X n
  coherent : ∀ {m n : ℕ} (h : n ≤ m),
    normalizedDVRReductionTransition l F X D hl h omega.obj ≫
        (normalizedDVRRes l F X h).map (reduction n).hom =
      (reduction m).hom ≫ integralDualizingExceptionalTransition l F D X hl h

/-- The coherent presentations required here exist, with the actual finite counits.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension).
Proof: choose a dimension bound for the finite-type scheme, then apply the integral
 dualizing proposition. Compose its normalized DVR counit comparisons with its
coherent finite-term origins. Their transition equation is precisely coherent. -/
theorem dualizingDatum_nonempty (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] : Nonempty (DualizingDatum l X D hl F) := by
  classical
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
  obtain ⟨ω, T, _, ⟨e, he⟩, _, hp, _⟩ := prop_coef_integral_dualizing D l hl F X d hd
  let : HasCountableProducts (completedIntegralDerivedCategory l F X D hl) :=
    integralOperationsDerivedCountableProducts l F X
  obtain ⟨p, δ, _, hi, hc⟩ := hp
  let r (n : ℕ) : (scalarReductionDerivedExtension l F X n).obj ω.obj ≅
      integralDualizingFiniteTerm l F D X n :=
    @asIso _ _ _ _ (normalizedDVRCounitComparison l F X D hl T ω.obj p n) (hi n) ≪≫ e n
  refine ⟨⟨ω, r, ?_⟩⟩
  intro m n h
  change normalizedDVRReductionTransition l F X D hl h ω.obj ≫
      (normalizedDVRRes l F X h).map
        (normalizedDVRCounitComparison l F X D hl T ω.obj p n ≫ (e n).hom) =
    (normalizedDVRCounitComparison l F X D hl T ω.obj p m ≫ (e m).hom) ≫
      integralDualizingExceptionalTransition l F D X hl h
  rw [Functor.map_comp, ← Category.assoc, ← hc m n h, Category.assoc, he h]
  simp only [integralDualizingFiniteComparison, Equiv.apply_symm_apply, Category.assoc]

/-- Completed finite-free extension preserves completeness on all complete inputs.
Source: blueprint order 2494, first paragraph
(blueprint: lem-coef-integral-finite-extension).
Proof: on a flat-term K-flat representative the finite-free basis commutes with
products in the Roos complex. Cofinality of uniformizer powers identifies its
completion unit with the target completion unit, so the latter is invertible. -/
theorem extension_complete (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) : IsSfDerivedComplete l L X
      ((integralScalarExtensionOfUniverses l E L ι X).obj K) := by
  apply (complete_iff_unrestricted l L X _).mpr
  exact unrestricted_complete_of_iso l L X (completion l E L ι X K hK)
    ((finiteFreeCompletedScalarComparison l E L ι X).2.1 K
      ((complete_iff_unrestricted l E X K).mp hK)).2

end WeilConjectures.IntegralFiniteExtension
