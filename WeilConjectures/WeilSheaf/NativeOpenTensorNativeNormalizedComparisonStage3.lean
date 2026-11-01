/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
public import WeilConjectures.WeilSheaf.NativeOpenTensorNativePairRestrictionStage3
public import WeilConjectures.WeilSheaf.NativeOpenTensorNativeSheafStage3
public import WeilConjectures.SixFunctors.NativeNormalizedRestrictionProof.NativeOpenTensorNativeTotalStage3

/-! The native normalized comparison used by open tensor restriction descent.
(blueprint: lem-sf-native-open-tensor-restriction-descent) -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 4096

attribute [local irreducible]
  CategoryTheory.OpenTensorRestrictionNormalization

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] OpenTensorDescentInput.r_add OpenTensorDescentInput.r_lim
  OpenTensorDescentInput.r_colim OpenTensorDescentInput.r_zero

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- Existence results supplied by the native sheaf, total, and pair stages. -/
structure NativeRestrictionStageInputs
    (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j)) : Prop where
  restriction_kflat : ∀ T, NativeIsKFlat k₀ l Z T →
    NativeIsKFlat k₀ l U
      (((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)).obj T)
  sheaf : Nonempty (SheafData k₀ l j s m)
  total : ∀ (sr : (nativeOpenTensorDescentInput k₀ l j).SB ⋙
      (nativeOpenTensorDescentInput k₀ l j).R ≅
      (nativeOpenTensorDescentInput k₀ l j).R.prod
        (nativeOpenTensorDescentInput k₀ l j).R ⋙
      (nativeOpenTensorDescentInput k₀ l j).SA),
    Nonempty (NativeNormalizedRestrictionProof.TotalData
      (nativeOpenTensorDescentInput k₀ l j) m sr)
  pair : Nonempty (NativePairRestrictionData k₀ l j)

/-- The native normalized comparison assembles the restriction component from the
native sheaf and total stages and the fully faithful pair restriction.

Source: Stacks 07A4 (lemma-pullback-tensor-product), 06YN, 06YS and 012Z.
(blueprint: new-sf-native-open-tensor-normalized-comparison-stage3)

Proof: take hR from `restriction_kflat`, choose the sheaf map `sr` of the sheaf stage
and the total comparison for `sr` of the total stage; the sheaf-stage HEq turns its
summand equation into the one for `m.sheafRestriction`. On native K-flat pairs P,T
compose the ambient model (by hm the native model of native_normalized_tensor_models),
the exact derived factorization of restriction, Q of the total comparison, the inverse
open model and the inverse factorizations of the restricted inputs (K-flat by hR).
Naturality of the models, of the total comparison and of the factorizations makes
this a natural isomorphism on K-flat pairs; full faithfulness of the pair stage
descends it to rho on all derived inputs, and cancelling the model and factorization
isomorphisms is the square of OpenTensorRestrictionNormalization. The same rho with
the native functor types gives the native field and its HEq. -/
theorem normalizedComparisonStage3
    (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (hm : NativeOpenTensorModelsCompatibility k₀ l j s m)
    (stages : NativeRestrictionStageInputs k₀ l j s m) :
    Nonempty (NativeOpenTensorRestrictionDescentData k₀ l j s m) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
