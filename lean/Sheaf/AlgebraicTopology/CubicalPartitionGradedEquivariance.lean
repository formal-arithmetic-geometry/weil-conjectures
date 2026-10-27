module

public import Sheaf.AlgebraicTopology.IntegralCubicalChainDiagonal
public import Mathlib.Algebra.Homology.Embedding.Extend

/-! # Graded cubical partition map and diagonal translation

Source: the agent-written algebraic expansion retained in the DAG, original integral
cubical diagonal proof steps 1 and 4
(blueprint: lem-sfb-cubical-partition-graded-equivariance).
The current blueprint direct-images proof, paragraph (3), gives the route location only;
it does not assert this cubical formula. An exact external reference remains WANTED.

The published partition formula is reused, with Mathlib's zero extension to integer
degrees. The conclusion concerns graded maps and does not impose a chain-map equation
on the partition map.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct

namespace IntegralLatticeCubical

/-- The existing tensor complex, extended by zero to every negative integer degree.
Source: the definition of `T` and its zero-degree convention in the DAG statement
(blueprint: lem-sfb-cubical-partition-graded-equivariance). -/
noncomputable def partitionTensorComplex (r : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℤ :=
  (HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).extend
    (ComplexShape.embeddingUpIntGE 0).op

/-- Canonical tensor-summand inclusion in integer total degree `n`. A negative factor
or an incorrect total degree gives the zero map. All nonzero data are the published
Mathlib tensor inclusion, composed with equality transports and zero-extension transport.
Source: the definition `T_n = direct sum of C_a tensor C_b` in the DAG statement
(blueprint: lem-sfb-cubical-partition-graded-equivariance). -/
noncomputable def partitionTensorInclusion (r : ℕ) (a b n : ℤ) :
    Chains r a ⊗[ℤ] Chains r b →ₗ[ℤ] (partitionTensorComplex r).X n :=
  if ha : 0 ≤ a then
    if hb : 0 ≤ b then
      if hn : ((a.toNat + b.toNat : ℕ) : ℤ) = n then
        ((HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).extendXIso
          (ComplexShape.embeddingUpIntGE 0).op (by simpa using hn)).inv.hom.comp
          ((HomologicalComplex.ιTensorObj (chainComplex r) (chainComplex r)
            a.toNat b.toNat (a.toNat + b.toNat) rfl).hom.comp
            (TensorProduct.map
              (LinearEquiv.cast (R := ℤ) (M := Chains r)
                (Int.toNat_of_nonneg ha).symm).toLinearMap
              (LinearEquiv.cast (R := ℤ) (M := Chains r)
                (Int.toNat_of_nonneg hb).symm).toLinearMap))
      else 0
    else 0
  else 0

/-- The already published finite partition map, transported to integer degrees on its
free basis. In negative degrees that basis is empty; no map is chosen from mere existence.
Source: the unique finite free extension in the DAG statement and proof step 4
(blueprint: lem-sfb-cubical-partition-graded-equivariance). -/
noncomputable def gradedPartitionComponent (r : ℕ) (n : ℤ) :
    Chains r n →ₗ[ℤ] (partitionTensorComplex r).X n :=
  Finsupp.linearCombination ℤ fun c ↦
    ((HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).extendXIso
      (ComplexShape.embeddingUpIntGE 0).op (by simpa using c.2.property)).inv
      (diagonalComponent r c.2.val.card (cell r (c.2.val.card : ℤ) c.1 c.2.val))

/-- Simultaneous translation in both tensor factors, in every integer degree, using
Mathlib's tensor of the existing translation maps and its canonical zero extension.
Source: diagonal translation on `T` in the DAG statement and proof step 5
(blueprint: lem-sfb-cubical-partition-graded-equivariance). -/
noncomputable def partitionTensorTranslate (r : ℕ) (n : ℤ) (w : Fin r → ℤ) :
    (partitionTensorComplex r).X n →ₗ[ℤ] (partitionTensorComplex r).X n :=
  (HomologicalComplex.extendMap
    (HomologicalComplex.tensorHom (translationMap r w) (translationMap r w))
    (ComplexShape.embeddingUpIntGE 0).op).f n |>.hom

/-- The signed tensor differential is well defined and squares to zero; the finite
partition formula defines the unique graded family and is equivariant for simultaneous
translation. The generator equation and generator-extensionality clause together say
existence and uniqueness with the prescribed basis values. The powerset has `2^|I|`
indices, counting terms before any collection or cancellation.

Source: the six-step agent-written proof in the DAG, expanding original integral
cubical diagonal steps 1 and 4
(blueprint: lem-sfb-cubical-partition-graded-equivariance).

Proof plan:
1. The signed differential on each tensor summand is induced by a bilinear map, by
`def-weil-pbc-module-tensor-product`. The direct sum has finite-support elements, so
these maps extend uniquely and agree with Mathlib's total tensor differential.
2. Apply the square-zero clause of `lem-sfb-integral-lattice-cubical-contraction`.
The two cross terms have coefficients `(-1)^(a-1)` and `(-1)^a`, which cancel. When
`a=0` its boundary is already zero. Pure tensors generate, so the square is zero on
all of the total complex, including negative degrees (the zero extension).
3. Subsets `A` of `I` parametrize the ordered partitions `(A,I \\ A)`, so there are
`2^|I|` terms. Disjointness gives `|A| + |I \\ A| = |I|`, proving homogeneity.
4. Use `def-weil-pbc-free-module`: every chain has a unique finite basis expansion.
Extend the prescribed generator values linearly. Any other family with these values
agrees on each finite expansion. Outside degrees zero through `r` the basis is empty,
so the map is zero. The construction here transports the existing `diagonalComponent`.
5. Translation extends from its values on cells by the same free-module property;
its tensor square extends by bilinearity. On generators zero translation is the identity
and composing translations adds their vectors. These identities extend to the modules.
6. Translation of a partition term has vertices `v+w` and `v+u_A+w`. Commutativity
identifies the second with `v+w+u_A`; partitions and signs are unchanged. Equality on
the free generators proves the asserted graded equivariance in every integer degree.
No commutation of the partition map with a differential is asserted. -/
theorem partitionGradedEquivariance (r : ℕ) :
    (∀ (a b : ℤ) (x : Chains r a) (y : Chains r b),
      (partitionTensorComplex r).d (a + b) (a + b - 1)
          (partitionTensorInclusion r a b (a + b) (x ⊗ₜ[ℤ] y)) =
        partitionTensorInclusion r (a - 1) b (a + b - 1)
            (boundary r a x ⊗ₜ[ℤ] y) +
          (a.negOnePow : ℤ) •
            partitionTensorInclusion r a (b - 1) (a + b - 1)
              (x ⊗ₜ[ℤ] boundary r b y)) ∧
    (∀ n : ℤ,
      (partitionTensorComplex r).d n (n - 1) ≫
        (partitionTensorComplex r).d (n - 1) (n - 1 - 1) = 0) ∧
    (∀ (n : ℤ) (v : Fin r → ℤ) (I : Directions r n),
      gradedPartitionComponent r n (cell r n v I.val) =
        ∑ A ∈ I.val.powerset, partitionSign r A (I.val \ A) •
          partitionTensorInclusion r (A.card : ℤ) ((I.val \ A).card : ℤ) n
            (cell r (A.card : ℤ) v A ⊗ₜ[ℤ]
              cell r ((I.val \ A).card : ℤ) (v + directionSum r A) (I.val \ A))) ∧
    (∀ P : (n : ℤ) → Chains r n →ₗ[ℤ] (partitionTensorComplex r).X n,
      (∀ (n : ℤ) (v : Fin r → ℤ) (I : Directions r n),
        P n (cell r n v I.val) = gradedPartitionComponent r n (cell r n v I.val)) →
      P = gradedPartitionComponent r) ∧
    (∀ I : Finset (Fin r), I.powerset.card = 2 ^ I.card ∧
      ∀ A ∈ I.powerset, (A.card : ℤ) + ((I \ A).card : ℤ) = (I.card : ℤ)) ∧
    (∀ n : ℤ, n < 0 ∨ (r : ℤ) < n → gradedPartitionComponent r n = 0) ∧
    (∀ (n : ℤ) (w : Fin r → ℤ),
      (gradedPartitionComponent r n).comp (translate r n w) =
        (partitionTensorTranslate r n w).comp (gradedPartitionComponent r n)) := by
  sorry

end IntegralLatticeCubical
