/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.Paper.NativeWeilTensorRingedBridgeData
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # K-flat transport for normalized native ringed tensors

The K-flat transport is the first independent field of the native ringed tensor
interface.  Its proof uses the underived tensor comparison and the additive
native equivalence, together with the ringed-site resolution theorem.
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
Transport acyclic-test K-flatness through the native additive equivalence.
Source: Stacks 06YS, 06YU and 0FPT.
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-flat).

Proof: identify the native tensor with the normalized ringed tensor by the
underived Hom comparison, then transport the acyclic-test condition through
`b.native`.  The ringed-site K-flat resolution theorem supplies the required
independent-coefficient condition for every native K-flat complex.
-/
theorem native_weil_tensor_ringed_kflat_flat :
    ∀ (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
      NativeTensorKFlat k₀ l X T P →
        CochainComplex.IsKFlatIndependentCoefficients (R := b.R)
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
