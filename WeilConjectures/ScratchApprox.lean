module

public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R₀ R₁ S₀ M₀ : Type) [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀] [AddCommGroup M₀] [Module S₀ M₀] [Module R₀ M₀] [IsScalarTower R₀ S₀ M₀]

#synth Module R₁ ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)
#synth Module (R₁ ⊗[R₀] S₀) ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)
#synth IsScalarTower R₁ (R₁ ⊗[R₀] S₀) ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)
#synth IsScalarTower R₀ R₁ ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)
#synth Module.Finite (R₁ ⊗[R₀] S₀) ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)
example (s : S₀) (r : R₁): (algebraMap S₀ (R₁ ⊗[R₀] S₀) s) = 1 ⊗ₜ s := rfl
