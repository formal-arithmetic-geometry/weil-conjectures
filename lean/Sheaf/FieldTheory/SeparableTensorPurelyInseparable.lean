module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Separable tensor purely inseparable field extensions

Source: literature/stacks-project/algebra.tex, Lemma Tag 07QH (blueprint:
lem-weil-pbc-separable-tensor-purely-inseparable-field)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

/--
The tensor product of a separable algebraic field extension with a finite purely
inseparable extension is a field and is finite purely inseparable over the first
field, with the expected dimension.

Source: literature/stacks-project/algebra.tex, Lemma Tag 07QH, proof first
paragraph (blueprint: lem-weil-pbc-separable-tensor-purely-inseparable-field).
The proof realizes the tensor product as the compositum using linear
 disjointness of separable and purely inseparable extensions, then uses a tensor
basis for the dimension and a Frobenius-power argument for pure inseparability.
-/
theorem separableTensor_purelyInseparable_isField
    (k : Type u) (k' : Type v) (L : Type w) [Field k] [Field k'] [Field L]
    [Algebra k k'] [Algebra k L] [Algebra.IsSeparable k k']
    [IsPurelyInseparable k L] [Module.Finite k L] :
    IsField (k' ⊗[k] L) ∧
      IsPurelyInseparable k' (k' ⊗[k] L) ∧
      Module.Finite k' (k' ⊗[k] L) ∧
      Module.finrank k' (k' ⊗[k] L) = Module.finrank k L := by
  sorry
