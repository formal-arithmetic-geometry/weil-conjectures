/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.IntrinsicKoszulCompletion
public import Sheaf.Paper.CompletionMap
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.RingTheory.NoetherianKoszulAugmentationProZero
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# The augmentation comparison of Koszul and quotient completions

Source: Weil conjectures blueprint, proper base change, order 1259
(blueprint: lemma-weil-pbc-koszul-quotient-limit).
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

noncomputable section

set_option backward.isDefEq.respectTransparency true

set_option maxHeartbeats 1600000 in
-- The statement elaborates several explicit product and cone constructions.
/-- The canonical comparison is induced by the quotient augmentation, including both
coordinates of the shifted cone. The tensor augmentation is fixed by its restriction to
the degree-zero unit and by vanishing on all other Koszul-degree summands.

Source: blueprint order 1259 (blueprint: lemma-weil-pbc-koszul-quotient-limit).
Proof: apply lem-weil-pbc-noetherian-koszul-augmentation-pro-zero to the generators.
The augmentation to I powers exists because f_j^(n+1) belongs to I^(n+1).
Its degree-zero component is the quotient, so it commutes strictly with transitions.
Constant module sheafification is exact (lem-weil-pbc-sheafification-exact and
lem-pc-sites-module-sheafification-interface), hence preserves the pro-zero cone maps.
Tensor using the same flat-term K-flat model at every level (lem-pc-kflat-resolution,
def-weil-derived-tensor). The tensor-cone identification has sign (-1)^p on the shifted
summand in tensor degree p. K-flatness preserves quasi-isomorphisms and zero derived maps.
Apply lem-weil-pbc-ringed-strict-tower-homotopy-limit: the induced limit map is invertible.
The explicit cone action uses the product augmentation in both coordinates; exact
countable pro-etale products identify this with the total right derived strict limit.
The levelwise unit composites are the quotient units, so the cone lifts give the stated
unit equation. Maps of K-flat representatives commute with tensor augmentations and
transitions before localization. These squares descend through quasi-isomorphisms and
therefore give naturality for all derived morphisms, independently of representatives. -/
theorem koszulQuotientLimit (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    (hf : Ideal.span (Set.range f) = d.ideal) :
    ∃ (v : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K) (n : ℕ),
        @Quiver.Hom (CochainComplex
          (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) inferInstance
          (koszulTensor X Λ r f M.complex n) (adicReductionComplex X d M n))
      (w : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K),
        @Quiver.Hom (CochainComplex
          (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) inferInstance
          (koszulCompletionComplex X Λ r f M.complex) (adicCompletionComplex X d M))
      (c : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K),
        intrinsicKoszulCompletion X Λ d r f hf K M.complex M.isKFlat M.realization ≅
          adicCompletionObject X d M),
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ), koszulTensorUnit X Λ r f M.complex n ≫ v K M n =
        adicReductionAugmentation X d M n) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ) (p q : ℤ) (hq : q ≠ 0),
        HomologicalComplex.ιMapBifunctor M.complex (koszulPowerSheaf X Λ r f n)
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
          (ComplexShape.up ℤ) p q (p + q) rfl ≫ (v K M n).f (p + q) = 0) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ), v K M (n + 1) ≫ adicReductionComplexStep X d M n =
        koszulTensorTransition X Λ r f M.complex n ≫ v K M n) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), w K M ≫ adicCompletionProjection X d M =
        CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f M.complex) ≫
          Limits.Pi.map (v K M)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (p : ℤ), (w K M).f p ≫
          (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d M)).v p (p + -1) rfl =
        (CochainComplex.mappingCocone.snd
          (koszulOneSubShift X Λ r f M.complex)).v p (p + -1) rfl ≫
            (Limits.Pi.map (v K M)).f (p + -1)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), (c K M).hom = (adicLocalization X Λ).map (w K M)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), intrinsicKoszulCompletionUnit X Λ d r f hf K M.complex
        M.isKFlat M.realization ≫ (c K M).hom = adicCompletionMap X d M) ∧
      (∀ (K L : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ L)
        (g : M.complex ⟶ N.complex)
        (τ : ∀ n : ℕ, koszulTensor X Λ r f M.complex n ⟶
          koszulTensor X Λ r f N.complex n)
        (σ : ∀ n : ℕ, adicReductionComplex X d M n ⟶ adicReductionComplex X d N n)
        (a : koszulCompletionComplex X Λ r f M.complex ⟶
          koszulCompletionComplex X Λ r f N.complex)
        (b : adicCompletionComplex X d M ⟶ adicCompletionComplex X d N),
        (∀ n, τ n = HomologicalComplex.mapBifunctorMap g
          (𝟙 (koszulPowerSheaf X Λ r f n))
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
          (ComplexShape.up ℤ)) →
        (∀ n, adicReductionAugmentation X d M n ≫ σ n =
          g ≫ adicReductionAugmentation X d N n) →
        a ≫ CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f N.complex) =
          CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f M.complex) ≫
            Limits.Pi.map τ →
        (∀ p : ℤ, a.f p ≫
          (CochainComplex.mappingCocone.snd (koszulOneSubShift X Λ r f N.complex)).v
            p (p + -1) rfl =
          (CochainComplex.mappingCocone.snd (koszulOneSubShift X Λ r f M.complex)).v
            p (p + -1) rfl ≫ (Limits.Pi.map τ).f (p + -1)) →
        b ≫ adicCompletionProjection X d N =
          adicCompletionProjection X d M ≫ Limits.Pi.map σ →
        (∀ p : ℤ, b.f p ≫ (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d N)).v p (p + -1) rfl =
          (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d M)).v p (p + -1) rfl ≫
              (Limits.Pi.map σ).f (p + -1)) →
        (c K M).hom ≫ (adicLocalization X Λ).map b =
          (adicLocalization X Λ).map a ≫ (c L N).hom) := by
  sorry

end

end AlgebraicGeometry.Scheme
