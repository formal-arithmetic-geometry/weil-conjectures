/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K9
-/
module

public import Sheaf.Paper.NativeWeilTensorRingedBridgeData
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Equivalence field of native K-flat localization

The roof and common-refinement argument for native K-flat complexes is isolated
as the equivalence field of the localization predicate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]

/-- The localization construction for native K-flat complexes is an equivalence.
Source: Stacks 06YS, 06YU and 0FPT.
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-localization-equivalence).

Proof: represent every derived morphism by a roof with a quasi-isomorphism on the
left, replace its vertex by a native K-flat complex, and use common refinements of
such replacements. This gives fullness and faithfulness of the functor induced by
`NativeTensorKFlat`; the same replacements give essential surjectivity. The
argument is valid for unbounded and zero complexes.
-/
theorem native_weil_tensor_ringed_kflat_localization_equivalence
    (hInv :
      ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeTensorKFlat k₀ l X T))).IsInvertedBy
        ((ObjectProperty.ι (NativeTensorKFlat k₀ l X T)) ⋙ DerivedCategory.Q)) :
    (Localization.Construction.lift
      ((ObjectProperty.ι (NativeTensorKFlat k₀ l X T)) ⋙ DerivedCategory.Q)
      hInv).IsEquivalence := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
