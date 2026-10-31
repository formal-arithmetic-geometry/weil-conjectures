/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryRingedTensorCoherence
public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusComparison
import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomNaturality

/-! # The explicit Frobenius model with ordinary tensor coherence retained -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The canonical Frobenius model, constructed independently of tensor coherence.
Source: the explicit native_frobenius_ringed_model construction
(blueprint: new-sf-native-frobenius-coherent-ringed-model). -/
def canonicalFrobeniusRingedModel
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    NativeFrobeniusRingedModel k₀ l X := by
  classical
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let g := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
  let _ := (ProEtale.NativeFrobenius.translation_continuous Y g).1
  let _ := (ProEtale.NativeFrobenius.translation_continuous Y g).2
  let H := Classical.choice (ProEtale.adicModuleHomComparisonCore l Y)
  let hc := ProEtale.NativeFrobenius.nativeFrobeniusComparison Y l g H
  exact {
    C := WeilConjectures.WeilFrobeniusAction.Site Y
    category := inferInstance
    pullbacks := Adjunction.hasLimitsOfShape_of_equivalence
      (AsSmall.equiv.{u, u + 1, u + 1} :
        Y.ProEt ≌ WeilConjectures.WeilFrobeniusAction.Site Y).inverse
    J := WeilConjectures.WeilFrobeniusAction.topology Y
    s := WeilConjectures.WeilFrobeniusAction.translation g
    R := ProEtale.NativeFrobenius.ring Y l
    a := ProEtale.NativeFrobenius.ringIso Y l g
    E := ProEtale.NativeFrobenius.equivalence Y l
    additive := inferInstance
    comparison := hc.choose
    hom := ProEtale.NativeFrobenius.homComparison Y l H
    hom_naturality := fun f h ↦
      ProEtale.NativeFrobenius.homComparison_naturality Y l H f h
    hom_frobenius := hc.choose_spec }

/-- Retain tensor coherence of the explicitly constructed canonical Frobenius model.
Source: canonical section tensor comparison
(blueprint: new-sf-native-frobenius-coherent-ringed-model).

Proof: unfold the explicit model's site, equivalence and Hom maps. They are
precisely those of the canonical ordinary coherence theorem for the proved
comparison core. Apply that theorem. The model definition uses no tensor
coherence theorem; this result supplies only its coherence property. -/
theorem native_frobenius_coherent_ringed_model
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    FrobeniusOrdinaryTensorCoherence (canonicalFrobeniusRingedModel k₀ l X) := by
  exact canonical_ordinary_ringed_tensor_coherence l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    (Classical.choice (ProEtale.adicModuleHomComparisonCore l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))

end AlgebraicGeometry.ProEtaleWeilSheaf
