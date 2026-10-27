/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.NativeWeilTensorRingedUnderivedData
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
  (adj : T ⊣₂ ihomBifunctor k₀ l X)

/-- The pointwise underived comparisons assemble into a bifunctor isomorphism.
Source: Stacks 06YS and 06YU (blueprint: lem-sf-native-weil-tensor-ringed-chain-data).

Proof: use the normalized uncurrying equation to identify both composites with the
same tensor--Hom mate.  Naturality in each variable follows from uniqueness of
mates under the two adjunctions; this is the underived naturality step needed by
the total-complex comparison. -/
theorem native_weil_tensor_ringed_underived_iso
    (U : NativeWeilRingedTensorUnderivedData b T adj) :
    ∃ e : (Functor.uncurry.obj T ⋙ b.native.functor) ≅
      (b.native.functor.prod b.native.functor) ⋙
        Functor.uncurry.obj
          (MonoidalCategory.curriedTensor
            (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)).flip,
      ∀ P Q : ProEtaleWeilSheaf k₀ l X,
        e.hom.app (P, Q) = (U.underived P Q).hom := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
