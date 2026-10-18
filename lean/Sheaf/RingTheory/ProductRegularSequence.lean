import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor-product concatenation of regular sequences

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-regular/
  sk-thm-regular.proof.md, Step 5b (blueprint: lem-pur-product-regular-sequence)

## Main statements

* `RingTheory.Sequence.isRegular_tensor_append` states that concatenating regular
  sequences from two commutative algebras over a field is regular in their algebra
  tensor product, with the canonical quotient and localization clauses.
-/

universe u v w

namespace RingTheory.Sequence

/--
Tensor-product concatenation of regular sequences over a field.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-regular/
  sk-thm-regular.proof.md, Step 5b (blueprint: lem-pur-product-regular-sequence).
The proof first tensors each successive injective multiplication map with the flat
vector space over the field, using quotient/base-change identifications; it then
uses the nonzero tensor-product quotient to obtain regularity.  Finally it applies
prime localization of weakly regular sequences.  The empty-list cases are included
because `Fin 0` is allowed.
-/
theorem isRegular_tensor_append
    (k : Type u) (R : Type v) (S : Type w)
    [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (r s : ℕ) (f : Fin r → R) (g : Fin s → S)
    (hf : IsRegular R (List.ofFn f))
    (hg : IsRegular S (List.ofFn g)) :
    IsRegular (TensorProduct k R S)
        (List.map (Algebra.TensorProduct.includeLeft (R := k) (S := k)) (List.ofFn f) ++
          List.map (Algebra.TensorProduct.includeRight (R := k)) (List.ofFn g)) ∧
      (∃ e :
          (TensorProduct k R S ⧸
              Ideal.ofList
                (List.map (Algebra.TensorProduct.includeLeft (R := k) (S := k)) (List.ofFn f) ++
                  List.map (Algebra.TensorProduct.includeRight (R := k)) (List.ofFn g)))
            ≃ₐ[k]
          TensorProduct k (R ⧸ Ideal.ofList (List.ofFn f))
            (S ⧸ Ideal.ofList (List.ofFn g)),
        ∀ (a : R) (b : S),
          e (Ideal.Quotient.mk
              (Ideal.ofList
                (List.map (Algebra.TensorProduct.includeLeft (R := k) (S := k)) (List.ofFn f) ++
                  List.map (Algebra.TensorProduct.includeRight (R := k)) (List.ofFn g)))
              (TensorProduct.tmul k a b)) =
            TensorProduct.tmul k
              (Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) a)
              (Ideal.Quotient.mk (Ideal.ofList (List.ofFn g)) b)) ∧
      Nontrivial
        (TensorProduct k R S ⧸
          Ideal.ofList
            (List.map (Algebra.TensorProduct.includeLeft (R := k) (S := k)) (List.ofFn f) ++
              List.map (Algebra.TensorProduct.includeRight (R := k)) (List.ofFn g))) ∧
      (∀ (q : Ideal (TensorProduct k R S)) [hq : q.IsPrime],
        Ideal.ofList
            (List.map (Algebra.TensorProduct.includeLeft (R := k) (S := k)) (List.ofFn f) ++
              List.map (Algebra.TensorProduct.includeRight (R := k)) (List.ofFn g)) ≤ q →
          IsRegular (Localization.AtPrime q)
              (List.map (algebraMap (TensorProduct k R S)
                (Localization.AtPrime q))
                (List.map (Algebra.TensorProduct.includeLeft (R := k) (S := k)) (List.ofFn f) ++
                  List.map (Algebra.TensorProduct.includeRight (R := k)) (List.ofFn g))) ∧
            (List.map (algebraMap (TensorProduct k R S)
              (Localization.AtPrime q))
              (List.map (Algebra.TensorProduct.includeLeft (R := k) (S := k)) (List.ofFn f) ++
                List.map (Algebra.TensorProduct.includeRight (R := k)) (List.ofFn g))).length =
              r + s) := by
  sorry

end RingTheory.Sequence
