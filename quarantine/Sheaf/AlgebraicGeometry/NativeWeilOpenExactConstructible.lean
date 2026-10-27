/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek

/-!
# Exact constructible open extension of native Weil sheaves

Source: WeilConjectures/WeilSheaf/OpenImmersion.lean, extensionByZero and its exactness
instances; SixFunctors/ProEtale/Adic/ExtensionByZero.lean, constructibility theorem;
Stacks Project, Tags 03DI and 03DJ.
(blueprint: lem-sf-native-weil-open-exact-constructible)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Native open extension is additive, preserves finite limits and colimits, and preserves
constructibility of the underlying sheaf.

Source: WeilConjectures/WeilSheaf/OpenImmersion.lean, lines 44-55, 92-105 and 138-150;
SixFunctors/ProEtale/Adic/ExtensionByZero.lean, lines 200-242; Stacks 03DI and 03DJ.
(blueprint: lem-sf-native-weil-open-exact-constructible)

Proof plan:
1. Base change preserves open immersions and quasi-compactness. Weakly-etale localization
   identifies the geometric open's pro-etale site with the slice. The coefficient restriction
   is literally the same locally finite continuous functions. Apply
   lem-weil-pbc-ringed-sheaf-slice-adjunction to obtain additive exact underlying extension.
2. The framework's extensionByZero lifts this functor by its Frobenius comparison. Naturality
   gives equivariant image arrows; faithful forgetting gives additivity. Exact conservative
   forgetting from the native abelian Weil categories detects exactness of image sequences
   (lem-sf-native-weil-constructible-abelian).
3. An additive exact functor preserves zero and finite biproducts, kernels and cokernels.
   Equalizers are kernels of differences and coequalizers are cokernels of differences.
   The usual finite product/equalizer and coproduct/coequalizer formulas give preservation of
   all finite limits and colimits, including the empty diagram.
4. At a point choose an affine neighbourhood V in the geometric target. Its intersection D
   with the geometric open is qcqs by open-immersion and quasi-compact base change and affine
   qcqs. Its reduced closed complement Z and D have constructible, disjoint covering images.
5. Pullback of the constructible sheaf to D is constructible by
   lem-sf-native-adic-constructible-pullback. Use lem-sf-native-adic-qcqs-stratification to
   obtain a finite constructible locally closed lisse stratification of D.
6. By lem-sf-native-adic-open-restrictions the extended sheaf restricts to the original on D
   and to zero on Z. Inverse-image composition identifies the nested module restrictions.
   Zero is lisse of rank zero. Apply lem-weil-pbc-constructible-stratification-assembly to the
   strata of D together with Z to stratify V.
7. These neighbourhoods establish constructibility on the geometric target. The framework's
   lifted functor has exactly this underlying sheaf. Empty pieces and zero sheaves are allowed.
-/
theorem extensionByZero_exact_constructible
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    (U T : Scheme.{u}) [U.Over (Spec (CommRingCat.of k₀))]
    [T.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    (extensionByZero k₀ l j).Additive ∧
      PreservesFiniteLimits (extensionByZero k₀ l j) ∧
      PreservesFiniteColimits (extensionByZero k₀ l j) ∧
      ∀ F : ProEtaleWeilSheaf k₀ l U,
        WeilSheaf.objectProperty k₀ l U F →
          WeilSheaf.objectProperty k₀ l T ((extensionByZero k₀ l j).obj F) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro F hF
  exact WeilSheaf.isAdicConstructibleSheaf_extensionByZero j F hF

end AlgebraicGeometry.ProEtaleWeilSheaf
