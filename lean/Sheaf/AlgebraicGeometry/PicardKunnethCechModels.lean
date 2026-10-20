/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso

/-! # Cech models for the quasi-coherent external product

Source: Stacks Project, Varieties, Tag 0BED, proof of varieties-lemma-kunneth.
(blueprint: lem-sc-picard-kunneth-cech-models).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum
namespace AlgebraicGeometry.Scheme.Modules

/-- Nonnegative Cech models and the geometric tensor-total comparison, before applying
field-linear Kunneth to their cohomology.
Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech and the proof
that this comparison is a quasi-isomorphism; Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-picard-kunneth-cech-models).

Proof: Use the actual global-sections complexes of the fixed injective resolutions,
restrict scalars along the structure maps and extend by zero to integer degrees.
The resolution, exact scalar restriction and zero-extension homology isomorphisms
give the comparisons alpha and beta. The negative-degree vanishing is proved by
the fact that no negative integer lies in the natural-number embedding's image.
Obtain a normalized cochain realization of externalCup from
picardExternalCupCochain_exists. The separate geometric theorem
picardExternalCupCochain_isIso proves its homology maps invertible by finite affine
Cech covers, two coefficient dimension-shifting inductions and the acyclic Leray
base case of Tag 0BED. Compose the induced homology isomorphism with the product
resolution comparison to define gamma. Its value on a tensor cycle is the cochain
normalization formula; the inverse factor comparisons cancel definitionally.
No equivalence or complex is selected from a holed mere-existence theorem.
No finite-dimensionality or nonempty-scheme assumption is introduced. -/
theorem picard_kunneth_cech_models (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (Limits.pullback.diagonal f)] [IsAffineHom (Limits.pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ∃ (A B : CochainComplex (ModuleCat.{w} k) ℤ),
      (∀ p : ℤ, p < 0 → IsZero (A.X p)) ∧
      (∀ q : ℤ, q < 0 → IsZero (B.X q)) ∧
      ∃ (alpha : ∀ p : ℕ, scalarCohomology f F p ≃ₗ[k] A.homology (p : ℤ))
        (beta : ∀ q : ℕ, scalarCohomology g G q ≃ₗ[k] B.homology (q : ℤ))
        (gamma : ∀ n : ℕ,
          (HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℤ)).homology (n : ℤ) ≃ₗ[k]
            scalarCohomology (Limits.pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G) n),
        ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
          (a : A.cycles (i.val.1 : ℤ)) (b : B.cycles (i.val.2 : ℤ))
          (z : (HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℤ)).cycles (n : ℤ)),
          (HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℤ)).iCycles (n : ℤ) z =
            HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℤ) (i.val.1 : ℤ) (i.val.2 : ℤ) (n : ℤ)
              (by
                change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
                exact_mod_cast i.property)
              ((A.iCycles (i.val.1 : ℤ) a) ⊗ₜ[k] (B.iCycles (i.val.2 : ℤ) b)) →
          gamma n ((HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℤ)).homologyπ (n : ℤ) z) =
            cast (congrArg (fun d ↦ ↥(scalarCohomology (Limits.pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G) d)) i.property)
              (externalCup f g F G i.val.1 i.val.2
                ((alpha i.val.1).symm (A.homologyπ (i.val.1 : ℤ) a))
                ((beta i.val.2).symm (B.homologyπ (i.val.2 : ℤ) b))) := by
  classical
  -- Eliminate the cup realization inside this proof; the models themselves are constructed.
  obtain ⟨c, hc⟩ := picardExternalCupCochain_exists f g F G
  let gamma : ∀ n : ℕ,
      (picardExternalTotal f g F G).homology (n : ℤ) ≃ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n :=
    fun n ↦ by
      letI := picardExternalCupCochain_isIso k X Y f g F G c hc n
      exact (asIso (HomologicalComplex.homologyMap c (n : ℤ))).toLinearEquiv.trans
        (picardScalarModelEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n)
  refine ⟨picardScalarModel f F, picardScalarModel g G,
    picardScalarModel_negative f F, picardScalarModel_negative g G,
    (fun p ↦ (picardScalarModelEquiv f F p).symm),
    (fun q ↦ (picardScalarModelEquiv g G q).symm), gamma, ?_⟩
  intro n i a b z hz
  -- The inverse comparisons cancel, and gamma applies the normalized homology map.
  exact hc n i a b z hz

end AlgebraicGeometry.Scheme.Modules
