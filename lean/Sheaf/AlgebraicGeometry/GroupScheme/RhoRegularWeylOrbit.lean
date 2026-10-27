/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-! # Regularity and Weyl orbit of the half sum of positive roots

Source: Milne, Algebraic Groups (2017), Appendix C.21--C.22 and Summary 21.41.
(blueprint: lem-sfb-rho-regular-weyl-orbit)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The half sum of positive roots is regular, and the longest Weyl element is its
unique negative orbit representative.

Source: Milne, Algebraic Groups (2017), Appendix C.21--C.22 and Summary 21.41.
(blueprint: lem-sfb-rho-regular-weyl-orbit)

Proof plan:
1. Use the reductive Borel-pair structure and the rank-one reflection theorem to
   obtain the finite reduced crystallographic root datum and its faithful Weyl action.
2. A simple reflection permutes all positive roots except its simple root, hence
   sends the half sum to the half sum minus that simple root and gives pairing one.
3. Average a positive definite inner product over the finite Weyl group; the simple
   roots define chambers, and the half sum lies in the open dominant chamber.
4. Chamber simple transitivity gives trivial stabilizer and a unique element carrying
   the positive chamber to its negative, which reverses all positive roots.
5. Reindexing the finite half sum gives the negative identity, the involution, and
   uniqueness. The empty root system is handled by the zero-dimensional span.
-/
theorem rho_regular_weyl_orbit
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (j : T ⟶ B) (hj : j ≫ iB = iT)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (b : P.Base) [P.IsReduced]
    (hconjG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X)
    (hconjB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ, b.IsPos α ↔
      @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (ρ : TensorProduct ℤ ℚ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (hρ : ρ = (1 / 2 : ℚ) •
      ∑ β ∈ (@Finset.filter Φ b.IsPos (Classical.decPred _) Finset.univ),
        TensorProduct.tmul ℤ (1 : ℚ) (P.root β)) :
    (∀ α ∈ b.support,
      (1 / 2 : ℚ) *
        ∑ β ∈ (@Finset.filter Φ b.IsPos (Classical.decPred _) Finset.univ),
          (P.toLinearMap (P.root β) (P.coroot α) : ℚ) = 1) ∧
    ∃ (act : RankOneRoots.Weyl iT →* Aut T)
      (ract : RankOneRoots.Weyl iT →*
        (TensorProduct ℤ ℚ
          (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ≃ₗ[ℚ]
         TensorProduct ℤ ℚ
          (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))),
      (∀ (n : RankOneRoots.normalizer iT) (A : CommAlgCat.{u} F)
        (t : StandardGroupSchemes.affine F A ⟶ T.X),
        t ≫ (act (QuotientGroup.mk n)).hom.hom.hom ≫ iT.hom.hom =
          (toUnit (StandardGroupSchemes.affine F A) ≫ n.val) * (t ≫ iT.hom.hom) *
            (toUnit (StandardGroupSchemes.affine F A) ≫ n.val)⁻¹) ∧
      (∀ (w : RankOneRoots.Weyl iT) (q : ℚ)
        (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))),
        ract w (TensorProduct.tmul ℤ q χ) =
          TensorProduct.tmul ℤ q (Additive.ofMul ((act w).inv ≫ χ.toMul))) ∧
      (∀ w : RankOneRoots.Weyl iT, ract w ρ = ρ ↔ w = 1) ∧
      ∃ w₀ : RankOneRoots.Weyl iT,
        (∀ w : RankOneRoots.Weyl iT,
          Set.image (fun β : Φ ↦ Additive.ofMul ((act w).inv ≫ β.val.toMul))
              {β : Φ | b.IsPos β} =
            Set.image (fun β : Φ ↦ -β.val) {β : Φ | b.IsPos β} ↔ w = w₀) ∧
        w₀ ^ 2 = 1 ∧ ract w₀ ρ = -ρ ∧
        (∀ w : RankOneRoots.Weyl iT, ract w ρ = -ρ ↔ w = w₀) ∧
        (Φ = ∅ →
          Submodule.span ℚ
              (Set.range (fun β : Φ ↦ TensorProduct.tmul ℤ (1 : ℚ) (P.root β))) = ⊥ ∧
            (∀ w : RankOneRoots.Weyl iT, w = 1) ∧ w₀ = 1) := by
  sorry

end AlgebraicGeometry
