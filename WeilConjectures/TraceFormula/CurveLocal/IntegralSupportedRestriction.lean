/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroTransfer

/-!

# The integral supported restriction and its reduction to the strictly local model

Let `c` be an endocorrespondence of `X` with fixed locus `F`. For a finite extension `E ⊆ ℚ̄_ℓ`
of `ℚ_ℓ` and an `𝒪_E`-complex `P` on `X × X`, the *integral supported restriction*
`ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P`
(`ProEtale.CondensedRing.Correspondence.FixedLocus.integralSupportedRestriction`) is the
exchange restriction of the fixed square with `𝒪_E`-coefficients (blueprint
`det-tf-supported-restriction`, with the integral coefficients of `sk-lem-tf-rational-model`).

This file also sets up the identification of `X × X` with the fibre product
`X ×_k X` of the classical model, with the factors interchanged
(`ProEtale.CondensedRing.swapPullbackToProd`): the library's correspondences have support
`(c₁, c₂)` and coefficients `K ⊠ D_X K`, the classical model
(`Etale.CurveLocalModel`) the transposed graph `(h, id)` and `D_X K ⊠ K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]

/-- The identification `X ×_k X ≅ (X ⨯ X).left` interchanging the factors: the first projection
of `X ⨯ X` corresponds to the second projection of the fibre product. -/
noncomputable def swapPullbackToProd (X : Over (Spec (.of k))) :
    pullback X.hom X.hom ⟶ (X ⨯ X).left :=
  (pullbackSymmetry X.hom X.hom).hom ≫ (Over.prodLeftIsoPullback X X).inv

instance (X : Over (Spec (.of k))) : IsIso (swapPullbackToProd X) := by
  unfold swapPullbackToProd
  infer_instance

@[reassoc (attr := simp)]
lemma swapPullbackToProd_fst (X : Over (Spec (.of k))) :
    swapPullbackToProd X ≫ (prod.fst : X ⨯ X ⟶ X).left = pullback.snd X.hom X.hom := by
  simp [swapPullbackToProd]

@[reassoc (attr := simp)]
lemma swapPullbackToProd_snd (X : Over (Spec (.of k))) :
    swapPullbackToProd X ≫ (prod.snd : X ⨯ X ⟶ X).left = pullback.fst X.hom X.hom := by
  simp [swapPullbackToProd]

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

namespace Correspondence.FixedLocus

variable (F : c.FixedLocus)

/-- Compact-support base change `Rc_! ⋙ LΔ^* ≅ Lι^* ⋙ Rd_!` in the fixed square, with
`𝒪_E`-coefficients. -/
noncomputable def integralLowerShriekBaseChangeIso :
    boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ c.support ⋙
        boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ (diag X) ≅
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ F.ι ⋙
        boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ F.d :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E F.isPullback
  asIso (boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E F.isPullback)

/-- The **integral supported restriction** `ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P` of the fixed square
with `𝒪_E`-coefficients (blueprint `det-tf-supported-restriction`, (2)): the exchange
restriction of the fixed square, the `Rd_! ⊣ Rd^!` adjoint of the inverse of compact-support base
change followed by `LΔ^*` of the counit of `Rc_! ⊣ Rc^!`. -/
noncomputable def integralSupportedRestriction
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleUpperStar _ ℓ F.ι).obj
        ((boundedConstructibleUpperShriek (Profinite.padicIntegersRingObj ℓ E) ℓ c.support).obj
          P) ⟶
      (boundedConstructibleUpperShriek _ ℓ F.d).obj
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ (diag X)).obj P) :=
  (CategoryTheory.mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction _ ℓ F.d)
    (TwoSquare.mk _ _ _ _ (F.integralLowerShriekBaseChangeIso E).inv)).natTrans.app P

end Correspondence.FixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
