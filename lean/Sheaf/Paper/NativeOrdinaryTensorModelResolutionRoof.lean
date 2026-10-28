/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.Paper.NativeWeilClosedModels

/-! # Common K-flat roofs for ordinary tensor resolutions

Source: Stacks 06YS, 06YU; blueprint step 1 of
`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-resolution-extension`.
(blueprint: lem-sf-native-weil-tensor-resolution-roof)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/--
Every map of second complexes admits a common K-flat roof whose two
augmentations are quasi-isomorphisms and whose comparison commutes up to a
chain homotopy.

Source: Stacks Tags 06YS and 06YU, common K-flat roof paragraph.  Resolve the
middle object of a homotopy-category common refinement by a K-flat complex and
compose its augmentation with the two refinement legs.  Two-out-of-three
preserves the quasi-isomorphism assertions, while the refinement equality
lifts to the displayed homotopy.
(blueprint: lem-sf-native-weil-tensor-resolution-roof)
-/
theorem native_ordinary_tensor_model_resolution_roof
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    ∀ (Q Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) (g : Q ⟶ Q'),
      ∃ (K K' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hK : NativeOrdinaryKFlat l Y K)
        (hK' : NativeOrdinaryKFlat l Y K')
        (q : K ⟶ Q) (q' : K' ⟶ Q') (u : K ⟶ K'),
        QuasiIso q ∧ QuasiIso q' ∧ Nonempty (Homotopy (u ≫ q') (q ≫ g)) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
