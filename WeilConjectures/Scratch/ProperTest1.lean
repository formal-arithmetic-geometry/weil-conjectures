module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

set_option profiler true in
example (k₀ : Type) [Field k₀] :
    (Field.toCommRing : CommRing (AlgebraicClosure k₀)) = AlgebraicClosure.instCommRing k₀ := rfl
