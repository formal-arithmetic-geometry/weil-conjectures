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
import Sheaf.AlgebraicGeometry.AffineModuleCechComparisonNatural
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteCohomologicalDimension
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Paper.CechComparisonMapNaturality
import Sheaf.Paper.CechCupPullbackCompat
import Sheaf.Paper.HigherDirectImagePresheaf

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

Proof: Choose finite affine covers U and V. Affine diagonal makes every finite
intersection affine; affine fibre products give the product cover W. Take A and B
to be the Cech complexes of F and G, restrict scalars to k, and extend by zero to
negative integer degrees. The scalar restriction of affine Cech comparison gives
alpha and beta in every natural degree. Refinement along both projections followed
by the signed Cech cup cochain map gives Tot(A tensor B) to Cech(W, external coefficients).
Its map on homology followed by affine Cech comparison is the map underlying gamma.
Prove this map is a quasi-isomorphism by the source's argument: affine-section
exactness and exactness of field tensor products produce maps of short exact
sequences of complexes in either coefficient. Their long exact sequences and the
five lemma give two out of three. The finite cohomological bounds and acyclic
embeddings reduce first one coefficient and then the other to acyclic coefficients.
For acyclic F and G, on an affine V in Y the complex for X times V is A tensor G(V).
Exactness of tensor identifies its cohomology with H(X,F) tensor G(V), which is zero
in positive degrees. On the affine basis the higher direct images under pr2 are
therefore zero and pr2-star of the external coefficients is Gamma(X,F) tensor G.
Expand Gamma(X,F) in a basis; cohomology commutes with this direct sum on qcqs Y.
Leray degeneration now shows that the product has only degree-zero cohomology, where
the comparison is the section tensor isomorphism. The tensor-total source is also
concentrated in degree zero: split each vector-space complex into its degree-zero
homology and contractible pieces, using complements of boundaries in cycles and of
cycles in terms. Tensoring a contractible piece with the other complex preserves its
contraction (with the signed contraction for the second factor). Only the tensor of
the degree-zero homologies remains. Thus the comparison is a quasi-isomorphism in
the acyclic base case. This completes both inductions.
Package the bijective homology maps as the linear equivalences gamma. Cech comparison
and cup/pullback compatibility give the displayed formula on cycle tensors. The
scalar Ext comparison computes the same maps on resolution representatives, so it
identifies this formula with externalCup. It is independent of the chosen product
cycle z because iCycles is monic. Empty schemes and zero coefficients are covered
by the zero-complex case, and no finite-dimensionality hypothesis is used. -/
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
                ((beta i.val.2).symm (B.homologyπ (i.val.2 : ℤ) b))) := by sorry

end AlgebraicGeometry.Scheme.Modules
