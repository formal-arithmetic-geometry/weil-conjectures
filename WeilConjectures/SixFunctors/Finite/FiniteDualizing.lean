/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingAffineRestriction
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingCoefficientNormalization
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingScalarRealization
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CoefficientCounitMateCocycle

/-! # Finite exceptional dualizing coefficient comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem finiteDualizing_compact_isIso {m n : ℕ} (h : n ≤ m)
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E m) X) :
    IsIso (Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E h)
      (finiteDualizingCompactification D X) K) := by
  let c := finiteDualizingCompactification D X
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have hi := (Etale.properFiniteCoefficientExtension (finiteDualizingQuotient l E h)
    c.g).1 ((Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E m)) c.i).mapDerivedCategory.obj K)
  unfold Etale.ExceptionalCoefficients.compactSupportMap
  infer_instance

private theorem finiteDualizing_etale_isIso (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m) : IsIso (finiteDualizingEtaleComparison l E D X h) := by
  have ha : ∀ x : X, ∃ (i : X.affineOpens) (y : (i : X.Opens)),
      (i : X.Opens).ι.base y = x := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, ⟨x, hx⟩, rfl⟩
  exact Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_jointlySurjective
    (finiteDualizingCoeff l E n) (ι := X.affineOpens)
    (fun V ↦ (V : X.Opens).ι) ha (finiteDualizingEtaleComparison l E D X h)
    (fun V ↦ finiteDualizing_affineRestriction_isIso l E D X hl h V V.property)

private theorem finiteDualizing_etale_unit (n : ℕ) :
    finiteDualizingEtaleComparison l E D X (le_refl n) =
      (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology _
        (finiteDualizingQuotient_id l E n)).hom.app (finiteDualizingEtaleTerm l E D X n) := by
  obtain ⟨hc, hN, _, _⟩ := finiteDualizing_compact_normalization l E D X
  have hi := finiteDualizing_compact_isIso l E D X (le_refl n)
    (finiteDualizingEtaleTerm l E D X n)
  have he := Adjunction.coefficientCounitMate_identity
    (finiteDualizingEtaleAdjunction l E D X n)
    (Etale.scalarExtension (finiteDualizingQuotient l E (le_refl n)) X)
    (Etale.scalarExtension (finiteDualizingQuotient l E (le_refl n)) (Spec (.of D.k)))
    (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology _
      (finiteDualizingQuotient_id l E n))
    (ProEtale.normalizedOriginScalarUnit (Spec (.of D.k)).smallEtaleTopology _
      (finiteDualizingQuotient_id l E n))
    (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))
    (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E (le_refl n))
      (Spec (.of D.k))) (hN n)
    (Etale.compactScalarMap (finiteDualizingQuotient l E (le_refl n))
      (finiteDualizingCompactification D X)) (hc n _)
  dsimp only [finiteDualizingEtaleTerm] at hi
  simpa only [finiteDualizingEtaleComparison, Etale.ExceptionalCoefficients.comparisonInverse,
    Etale.compactScalarMap, finiteDualizingEtaleTerm, finiteDualizingEtaleCounit,
    dif_pos hi] using he

private theorem finiteDualizing_etale_cocycle {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    (Etale.scalarExtension (finiteDualizingQuotient l E hmn) X).map
        (finiteDualizingEtaleComparison l E D X hrm) ≫
      finiteDualizingEtaleComparison l E D X hmn =
    (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology _ _ _
      (finiteDualizingQuotient_comp l E hrm hmn)).hom.app
        (finiteDualizingEtaleTerm l E D X r) ≫
      finiteDualizingEtaleComparison l E D X (hmn.trans hrm) := by
  obtain ⟨_, _, hc, hN⟩ := finiteDualizing_compact_normalization l E D X
  let a := finiteDualizingEtaleAdjunction l E D X r
  let b := finiteDualizingEtaleAdjunction l E D X m
  let c := finiteDualizingEtaleAdjunction l E D X n
  let tcAB := Etale.scalarExtension (finiteDualizingQuotient l E hrm) X
  let tdAB := Etale.scalarExtension (finiteDualizingQuotient l E hrm) (Spec (.of D.k))
  let tcBC := Etale.scalarExtension (finiteDualizingQuotient l E hmn) X
  let tdBC := Etale.scalarExtension (finiteDualizingQuotient l E hmn) (Spec (.of D.k))
  let tcAC := Etale.scalarExtension (finiteDualizingQuotient l E (hmn.trans hrm)) X
  let tdAC := Etale.scalarExtension (finiteDualizingQuotient l E (hmn.trans hrm))
    (Spec (.of D.k))
  have hiAB := finiteDualizing_compact_isIso l E D X hrm (finiteDualizingEtaleTerm l E D X r)
  have hiBC := finiteDualizing_compact_isIso l E D X hmn (finiteDualizingEtaleTerm l E D X m)
  have hiAC := finiteDualizing_compact_isIso l E D X (hmn.trans hrm)
    (finiteDualizingEtaleTerm l E D X r)
  have hiBC' := finiteDualizing_compact_isIso l E D X hmn
    (tcAB.obj (finiteDualizingEtaleTerm l E D X r))
  change IsIso ((Etale.compactScalarMap (finiteDualizingQuotient l E hrm)
    (finiteDualizingCompactification D X)).app ((finiteDualizingEtaleExceptional l E D X r).obj
      (Etale.constantComplex (finiteDualizingCoeff l E r) (Spec (.of D.k))))) at hiAB
  change IsIso ((Etale.compactScalarMap (finiteDualizingQuotient l E hmn)
    (finiteDualizingCompactification D X)).app ((finiteDualizingEtaleExceptional l E D X m).obj
      (Etale.constantComplex (finiteDualizingCoeff l E m) (Spec (.of D.k))))) at hiBC
  change IsIso ((Etale.compactScalarMap (finiteDualizingQuotient l E (hmn.trans hrm))
    (finiteDualizingCompactification D X)).app ((finiteDualizingEtaleExceptional l E D X r).obj
      (Etale.constantComplex (finiteDualizingCoeff l E r) (Spec (.of D.k))))) at hiAC
  change IsIso ((Etale.compactScalarMap (finiteDualizingQuotient l E hmn)
    (finiteDualizingCompactification D X)).app (tcAB.obj
      ((finiteDualizingEtaleExceptional l E D X r).obj
      (Etale.constantComplex (finiteDualizingCoeff l E r) (Spec (.of D.k)))))) at hiBC'
  have he := Adjunction.coefficientCounitMate_cocycle a b c
    tcAB tdAB tcBC tdBC tcAC tdAC
    (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology _ _ _
      (finiteDualizingQuotient_comp l E hrm hmn))
    (ProEtale.pbcFixedScalarExtensionComp (Spec (.of D.k)).smallEtaleTopology _ _ _
      (finiteDualizingQuotient_comp l E hrm hmn))
    (Etale.constantComplex (finiteDualizingCoeff l E r) (Spec (.of D.k)))
    (Etale.constantComplex (finiteDualizingCoeff l E m) (Spec (.of D.k)))
    (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))
    (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E hrm)
      (Spec (.of D.k)))
    (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E hmn)
      (Spec (.of D.k)))
    (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E (hmn.trans hrm))
      (Spec (.of D.k))) (hN hrm hmn)
    (Etale.compactScalarMap (finiteDualizingQuotient l E hrm)
      (finiteDualizingCompactification D X))
    (Etale.compactScalarMap (finiteDualizingQuotient l E hmn)
      (finiteDualizingCompactification D X))
    (Etale.compactScalarMap (finiteDualizingQuotient l E (hmn.trans hrm))
      (finiteDualizingCompactification D X)) (hc hrm hmn _)
  dsimp only [Etale.compactScalarMap] at hiAB hiBC hiAC
  have he' : finiteDualizingEtaleComparison l E D X (hmn.trans hrm) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology _ _ _
        (finiteDualizingQuotient_comp l E hrm hmn)).inv.app
          (finiteDualizingEtaleTerm l E D X r) ≫
        tcBC.map (finiteDualizingEtaleComparison l E D X hrm) ≫
          finiteDualizingEtaleComparison l E D X hmn := by
    simpa only [finiteDualizingEtaleComparison,
      Etale.ExceptionalCoefficients.comparisonInverse,
      dif_pos hiAB, dif_pos hiBC, dif_pos hiAC, Etale.compactScalarMap,
      finiteDualizingEtaleTerm, finiteDualizingEtaleCounit,
      a, b, c, tcAB, tdAB, tcBC, tdBC, tcAC, tdAC] using he
  rw [he']
  simp only [Iso.hom_inv_id_app_assoc]
  rfl

/-- Finite dualizing coefficient change, with the actual counit, quotient cocycle,
identity, and finite pro-etale realization. Natural level n means exponent n+1.
Source: current blueprint order 2484, lem-coef-finite-dualizing and its proof
(blueprint: lem-coef-finite-dualizing).
Proof:
1. The structure morphism is compactifiable by Nagata over the Noetherian field.
The ordinary etale exceptional adjunction gives the specified counit at A_s.
2. The regular constant object has Tor amplitude [0,0]. Verdier preservation on
strata implies that its exceptional dual is bounded constructible of finite Tor
amplitude. Consequently the compact-support coefficient comparison applies there.
Its proper/open mate is the published comparison of lem-fix-compact-support-coefficient-change.
3. Transpose its inverse followed by extension of epsilon and the regular scalar-unit
isomorphism. This is exactly finiteDualizingEtaleComparison; the adjunction triangle
identities give the displayed counit equation.
4. Localize on an affine chart and embed the chart into affine space. Composition of
adjoints identifies omega with closed exceptional image of the shifted Tate line.
Affine-space adjunction and finite closed shriek coefficient change show that this
very counit-defined map is invertible. The composite counit identity identifies the
local map with the global map, so these calculations agree on overlaps.
5. Transpose successive comparisons, use naturality, and paste the compact-support
coefficient comparisons. Their normalized scalar associator gives the cocycle;
the identity quotient and scalar-unit normalization give the unit equation.
6. The comparison-site unit identifies the etale dualizing term with the prescribed
sfFiniteExceptional term. The coefficient restriction square is normalized on scalar
sections. Transporting the scalar adjunct through these very identifications gives
integralDualizingExceptionalTransition. Conjugating the two scalar adjunctions makes
its intrinsic adjunct invertible and gives the same identity and cocycle equations.
No ambient adjunction on arbitrary pro-etale sheaves is asserted. -/
theorem finiteDualizingCoefficientComparisons (hl : l ≠ D.p) :
    (∀ {m n : ℕ} (h : n ≤ m),
      IsIso (finiteDualizingCompactComparison l E D X h) ∧
      IsIso (finiteDualizingEtaleComparison l E D X h) ∧
      (finiteDualizingEtaleSupport l E D X n).map
          (finiteDualizingEtaleComparison l E D X h) ≫
        finiteDualizingEtaleCounit l E D X n =
      Etale.ExceptionalCoefficients.comparisonInverse (finiteDualizingQuotient l E h)
          (finiteDualizingCompactification D X) (finiteDualizingEtaleTerm l E D X m) ≫
        (Etale.scalarExtension (finiteDualizingQuotient l E h) (Spec (.of D.k))).map
          (finiteDualizingEtaleCounit l E D X m) ≫
        (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
          (Spec (.of D.k))).hom) ∧
    (∀ n : ℕ, finiteDualizingEtaleComparison l E D X (le_refl n) =
      (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology _
        (finiteDualizingQuotient_id l E n)).hom.app (finiteDualizingEtaleTerm l E D X n)) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      (Etale.scalarExtension (finiteDualizingQuotient l E hmn) X).map
          (finiteDualizingEtaleComparison l E D X hrm) ≫
        finiteDualizingEtaleComparison l E D X hmn =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology _ _ _
        (finiteDualizingQuotient_comp l E hrm hmn)).hom.app
          (finiteDualizingEtaleTerm l E D X r) ≫
        finiteDualizingEtaleComparison l E D X (hmn.trans hrm)) ∧
    (∀ {m n : ℕ} (h : n ≤ m),
      IsIso (integralDualizingFiniteComparison l E D X hl h)) ∧
    (∀ n : ℕ, integralDualizingExceptionalTransition l E D X hl (le_refl n) ≫
      (normalizedDVRResUnit l E X n).hom.app (integralDualizingFiniteTerm l E D X n) = 𝟙 _) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      integralDualizingExceptionalTransition l E D X hl (hmn.trans hrm) ≫
        (normalizedDVRResComp l E X hrm hmn).inv.app (integralDualizingFiniteTerm l E D X n) =
      integralDualizingExceptionalTransition l E D X hl hrm ≫
        (normalizedDVRRes l E X hrm).map
          (integralDualizingExceptionalTransition l E D X hl hmn)) := by
  have hv : ∀ {m n : ℕ} (h : n ≤ m),
      IsIso (finiteDualizingEtaleComparison l E D X h) :=
    fun h ↦ finiteDualizing_etale_isIso l E D X hl h
  have hu := finiteDualizing_etale_unit l E D X
  have hc := fun {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) ↦
    finiteDualizing_etale_cocycle l E D X hrm hmn
  obtain ⟨hi, hunit, hcomp⟩ := finiteDualizing_scalar_realization l E X
    (finiteDualizingEtaleTerm l E D X) (integralDualizingFiniteTerm l E D X)
    (finiteDualizingOrigin l E D X) (fun h ↦ finiteDualizingEtaleComparison l E D X h)
    (fun h ↦ hv h) hu (fun h₁ h₂ ↦ hc h₁ h₂)
  refine ⟨?_, hu, fun h₁ h₂ ↦ hc h₁ h₂, ?_, hunit, fun h₁ h₂ ↦ hcomp h₁ h₂⟩
  · intro m n h
    exact ⟨finiteDualizing_compact_isIso l E D X h _, hv h,
      ((finiteDualizingEtaleAdjunction l E D X n).homEquiv _ _).symm_apply_apply _⟩
  · intro m n h
    exact hi h

end WeilConjectures
