/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.Paper.NativeWeilTensorRingedBridgeData
import Sheaf.Paper.NativeWeilTensorRingedKFlatLocalizationEquivalence

/-! # Localization for normalized native ringed tensors

The localization assertion is the second independent field of the native
ringed tensor interface.  It packages the roof and K-flat replacement argument
for the native acyclic-test predicate.
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

/--
Native K-flat complexes localize to the unbounded derived category.
Source: Stacks 06YS, 06YU and 0FPT.
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-localization).

Proof: use the native-to-ringed K-flat comparison and the homotopy
localization criterion.  K-flat replacements produce roofs in the native
subcategory, and common refinements give full faithfulness and essential
surjectivity, including unbounded and zero complexes.
-/
theorem native_weil_tensor_ringed_kflat_localization :
    ((ObjectProperty.ι (NativeTensorKFlat k₀ l X T)) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeTensorKFlat k₀ l X T))) := by
  let P := ObjectProperty.ι (NativeTensorKFlat k₀ l X T)
  let W := (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage P
  let L := P ⋙ DerivedCategory.Q
  have hInv : W.IsInvertedBy L := by
    intro A B f hf
    change IsIso (DerivedCategory.Q.map f.hom)
    change (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)) f.hom at hf
    exact Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)) f.hom hf
  refine { inverts := hInv, isEquivalence := ?_ }
  exact native_weil_tensor_ringed_kflat_localization_equivalence T hInv

end AlgebraicGeometry.ProEtaleWeilSheaf
