/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechExact

import Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators
import Sheaf.Algebra.Homology.TensorKunnethNat

/-! # Natural Cech cup and its scalar-model comparison

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech;
Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-picard-external-cup-left-cech-comparison).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct DirectSum
namespace AlgebraicGeometry.Scheme.Modules

/-- A natural transformation between the two concrete Cech functors realizes
external cup on homology. This lemma concerns a single varying coefficient,
without an exact sequence, exactness assertion or chosen normalized maps.

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech and the
coefficient diagram following it; Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-picard-external-cup-left-cech-comparison).

Proof: Refine the covers pulled back from the two factors to their product cover.
The sectionwise adjunction units, restrictions and tensor pairing give a k-linear
signed cup map from the tensor total to the product Cech complex. Its Leibniz rule
makes this a cochain map. The refinement maps and tensor pairing commute with
coefficient morphisms on every tuple; thus the maps form a natural transformation
on all left coefficient modules, including those that are not quasi-coherent.
For a quasi-coherent coefficient F, affine Cech comparison, exact restriction of
scalars and the fixed injective resolution comparison identify product Cech
homology with scalar-model homology. On the tensor side, apply field tensor
Kunneth to the Cech complexes and the scalar models, and tensor their factor
comparison isomorphisms. This gives a and b in every natural degree.
To check the equation for any normalized d, lift both factor homology classes to
cycles. The Cech refinement/cup compatibility identifies the image of each tensor
cycle under the natural transformation with externalCup of the factor classes.
The defining normalization of d gives the same value. Tensor Kunneth's cycle
formula and the spanning property of pure tensors and direct-sum inclusions imply
equality of the transported homology maps. This argument uses no invertibility
of external cup and no connecting homomorphisms. Empty covers and zero coefficients
give zero vector spaces; in degree zero the sole summand is indexed by (0,0). -/
theorem picardExternalCup_left_cech_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (G : Y.Modules) [G.IsQuasicoherent] :
    ∃ θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G,
      ∀ (F : X.Modules) (_ : F.IsQuasicoherent)
        (d : picardExternalTotal f g F G ⟶
          picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)),
        IsPicardExternalCupCochain f g F G d → ∀ n : ℕ,
          ∃ (a : ((picardLeftTensorCechFunctor f g G).obj F).homology (n : ℤ) ≅
              (picardExternalTotal f g F G).homology (n : ℤ))
            (b : ((picardLeftProductCechFunctor f g G).obj F).homology (n : ℤ) ≅
              (picardScalarModel (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G)).homology (n : ℤ)),
            HomologicalComplex.homologyMap (θ.app F) (n : ℤ) ≫ b.hom =
              a.hom ≫ HomologicalComplex.homologyMap d (n : ℤ) := by
  classical
  obtain ⟨θ, hθ⟩ := picardExternalCup_left_cech_generators f g G
  refine ⟨θ, ?_⟩
  intro F hF d hd n
  let A := picardScalarModel f F
  let B := picardScalarModel g G
  let T := picardExternalTotal f g F G
  obtain ⟨e, b, he⟩ := hθ F hF n
  obtain ⟨s, hs⟩ := HomologicalComplex.tensor_kunneth_nat A B
    (picardScalarModel_negative f F) (picardScalarModel_negative g G) n
  let a := (e.symm.trans s).toModuleIso
  refine ⟨a, b, ?_⟩
  have hmaps :
      (b.hom.hom.comp (HomologicalComplex.homologyMap (θ.app F) (n : ℤ)).hom).comp
          e.toLinearMap =
        (HomologicalComplex.homologyMap d (n : ℤ)).hom.comp s.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.ext'
    intro x y
    obtain ⟨x', hx⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ (i.val.1 : ℤ))).mp
      inferInstance x
    obtain ⟨y', hy⟩ := (ModuleCat.epi_iff_surjective (B.homologyπ (i.val.2 : ℤ))).mp
      inferInstance y
    obtain ⟨z, hz, hsz⟩ := hs i x' y'
    apply (picardScalarModelEquiv (pullback.fst f g ≫ f)
      (externalCupCoefficients f g F G) n).injective
    change picardScalarModelEquiv (pullback.fst f g ≫ f)
      (externalCupCoefficients f g F G) n
      (b.hom (HomologicalComplex.homologyMap (θ.app F) (n : ℤ)
        (e (DirectSum.lof k _ _ i (x ⊗ₜ[k] y))))) =
      picardScalarModelEquiv (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G) n
        (HomologicalComplex.homologyMap d (n : ℤ)
          (s (DirectSum.lof k _ _ i (x ⊗ₜ[k] y))))
    rw [he]
    have hsz' : s (DirectSum.lof k _ _ i (x ⊗ₜ[k] y)) = T.homologyπ (n : ℤ) z := by
      simpa only [A, B, T, picardExternalTotal, hx, hy] using hsz
    rw [hsz', hd n i x' y' z hz, hx, hy]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change _ = (HomologicalComplex.homologyMap d (n : ℤ)).hom (s (e.symm x))
  have h := LinearMap.congr_fun hmaps (e.symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at h
  exact h


end AlgebraicGeometry.Scheme.Modules
