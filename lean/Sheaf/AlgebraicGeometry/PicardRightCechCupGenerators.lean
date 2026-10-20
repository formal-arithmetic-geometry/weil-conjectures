/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.AlgebraicGeometry.PicardRightCechCupConstruction
public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.DirectSum.Module
import WeilConjectures.Algebra.Homology.TensorKunnethNaturalComplexes
import Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison

/-! # Specified external Cech cup on factor homology generators

Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech; Tags 01FD, 07MB, 0FKV.
(blueprint: lem-sc-picard-right-cech-cup-generators).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct DirectSum
namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def summandSignEquiv {k : Type w} [Field k]
    {I : Type*} (M : I → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    (d : I → ℕ) : (⨁ i, M i) ≃ₗ[k] ⨁ i, M i :=
  DirectSum.congrLinearEquiv fun i ↦ LinearEquiv.smulOfUnit ((-1 : kˣ) ^ d i)

private theorem summandSignEquiv_lof {k : Type w} [Field k]
    {I : Type*} [DecidableEq I] (M : I → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    (d : I → ℕ) (i : I) (x : M i) :
    summandSignEquiv (k := k) M d (DirectSum.lof k I M i x) =
      (-1 : ℤ) ^ d i • DirectSum.lof k I M i x := by
  classical
  simp only [summandSignEquiv, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
    LinearEquiv.coe_coe]
  change DirectSum.lof k I M i (((-1 : k) ^ d i) • x) = _
  rw [_root_.map_smul, ← Int.cast_smul_eq_zsmul k, Int.cast_pow, Int.cast_neg, Int.cast_one]


/-- The specified external Cech cup takes each pure factor-homology tensor to
external cup, in compatible Cech comparison coordinates. This statement concerns
only generators of the direct sum, and does not compare with scalar-total cycles.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech; Tags 01FD, 07MB, 0FKV.
(blueprint: lem-sc-picard-right-cech-cup-generators).

Proof: The affine diagonal criterion makes each nonempty finite factor intersection
affine. Intersections of the product cover are products of these affine opens over
Spec k and are affine; the product cover covers the fibre product. Pullback and tensor
preserve quasi-coherence. Apply the canonical affine Cech comparisons to the two
factors and the product coefficient. Restriction of scalars is exact and commutes
with the finite products in each Cech term. Compose the product comparison with the
inverse fixed-resolution comparison and extension homology to obtain b. Tensor the
factor comparisons on each direct-sum summand, then apply tensor Kunneth to the
extended factor Cech complexes. The canonical comparison between extension of the
natural tensor total and the tensor total of extensions yields a comparison.
Precompose it with the direct sum of scalar automorphisms (-1)^(p*q) on its
(p,q) tensor-homology summands. These are units over every field, so this gives
the equivalence e. The signed cycle formula and linearity of all comparisons
then give the displayed unsigned generator formula.
For x and y, lift their images under the factor comparisons to Cech cycles. Tensor
Kunneth represents their summand tensor by the total tensor cycle. The given hθ
identifies its image tuple by tuple with the front X section and back Y section
pulled back by the projection adjunction units and tensored. Refinement/pullback
compatibility and Cech/sheaf-cup compatibility send this class under the canonical
product comparison to externalCup of the factor classes. The fixed resolution
comparisons identify those classes with the displayed scalar-model equivalences.
The cast implements the equality p+q=n. All choices of comparisons here are made
together with this formula; independent rescaling of b is not allowed. Empty covers
cover only empty schemes, whose coefficient cohomology vanishes. Zero coefficients
likewise give zero spaces. In degree zero the formula is the section tensor pairing. -/
theorem picardRightCechCup_generators
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (θ : picardRightTensorCechFunctor f g U V F ⟶
      picardRightProductCechFunctor f g U V F)
    (hθ : IsPicardRightCechCup f g U V F θ)
    (G : Y.Modules) [G.IsQuasicoherent] (n : ℕ) :
        ∃ (e : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
              (picardScalarModel f F).homology (i.val.1 : ℤ) ⊗[k]
                (picardScalarModel g G).homology (i.val.2 : ℤ)) ≃ₗ[k]
              ((picardRightTensorCechFunctor f g U V F).obj G).homology (n : ℤ))
          (b : ((picardRightProductCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
            (picardScalarModel (pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G)).homology (n : ℤ)),
          ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
            (x : (picardScalarModel f F).homology (i.val.1 : ℤ))
            (y : (picardScalarModel g G).homology (i.val.2 : ℤ)),
            picardScalarModelEquiv (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) n
              (b.hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
                (e (DirectSum.lof k _ _ i (x ⊗ₜ[k] y))))) =
              cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) d)) i.property)
                (externalCup f g F G i.val.1 i.val.2
                  (picardScalarModelEquiv f F i.val.1 x)
                  (picardScalarModelEquiv g G i.val.2 y)) := by
  classical
  let A := (picardCechFunctor f U).obj F
  let B := (picardCechFunctor g V).obj G
  let T := HomologicalComplex.mapBifunctor A B
    (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ)
  obtain ⟨alpha, beta, b, hab⟩ := picardRightCechCup_cycle_comparison
    f g F U V hU hV hUc hVc θ hθ G
  obtain ⟨e, he⟩ := HomologicalComplex.tensor_kunneth_natural_complexes A B n
  let s := DirectSum.congrLinearEquiv fun i : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
    TensorProduct.congr (alpha i.val.1).symm (beta i.val.2).symm
  let t := T.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl
  let M := fun i : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
    (picardScalarModel f F).homology (i.val.1 : ℤ) ⊗[k]
      (picardScalarModel g G).homology (i.val.2 : ℤ)
  let r := summandSignEquiv (k := k) M (fun i ↦ i.val.1 * i.val.2)
  refine ⟨r.trans ((s.trans e).trans t.symm.toLinearEquiv), b n, ?_⟩
  intro i x y
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ i.val.1)).mp
    inferInstance ((alpha i.val.1).symm x)
  obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective (B.homologyπ i.val.2)).mp
    inferInstance ((beta i.val.2).symm y)
  obtain ⟨z, hz, hez⟩ := he i a v
  have hx : alpha i.val.1 (A.homologyπ _ a) = x := by
    rw [ha, LinearEquiv.apply_symm_apply]
  have hy : beta i.val.2 (B.homologyπ _ v) = y := by
    rw [hv, LinearEquiv.apply_symm_apply]
  have hs : s (DirectSum.lof k _ _ i (x ⊗ₜ[k] y)) =
      DirectSum.lof k _ _ i ((A.homologyπ _ a) ⊗ₜ[k] (B.homologyπ _ v)) := by
    simp only [s, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
      LinearEquiv.coe_coe, TensorProduct.congr_tmul, ← ha, ← hv]
  change picardScalarModelEquiv (pullback.fst f g ≫ f)
    (externalCupCoefficients f g F G) n
    ((b n).hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
      (t.inv (e (s (r (DirectSum.lof k _ _ i (x ⊗ₜ[k] y)))))))) = _
  rw [summandSignEquiv_lof, map_zsmul, map_zsmul, map_zsmul,
    map_zsmul, map_zsmul, map_zsmul, hs, hez]
  dsimp only [A] at hx
  dsimp only [B] at hy
  simpa only [hx, hy] using hab n i a v z hz

end AlgebraicGeometry.Scheme.Modules
