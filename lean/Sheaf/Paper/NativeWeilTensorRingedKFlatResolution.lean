/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.NativeWeilTensorRingedBridgeData
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Native K-flat resolutions

The native acyclic-test K-flat predicate is resolving: every complex admits a
quasi-isomorphism from a complex satisfying the predicate.  This is the density
input for the localization equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]

/-- Every native complex has a native K-flat quasi-isomorphic replacement.
Source: Stacks 06YS, the unbounded K-flat replacement construction.
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-resolution)

The construction resolves an arbitrary complex by the telescope of its bounded
truncation replacements.  Each truncation replacement has native K-flat terms;
the countable telescope remains native K-flat by closure under sums and cones,
and its augmentation to the original complex is a quasi-isomorphism.  The
construction is unbounded and also applies to the zero complex.
-/
theorem native_weil_tensor_ringed_kflat_resolution :
    let W₀ := HomologicalComplex.quasiIso
      (ProEtaleWeilSheaf k₀ l X) (.up ℤ)
    W₀.HasRightCalculusOfFractions ∧
      let P : ObjectProperty (CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
        NativeTensorKFlat k₀ l X T
      ∀ K : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
        ∃ (P' : P.FullSubcategory) (s : P.ι.obj P' ⟶ K), W₀ s := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
