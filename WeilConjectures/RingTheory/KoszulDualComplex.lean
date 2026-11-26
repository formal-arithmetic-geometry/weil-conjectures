/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# The total dual Koszul complex

The signed total `Hom` complex `Hom_A^•(K_A(f), A)` of the Koszul complex.

## Main definitions

* `koszulDualComplex`: signed total Hom of the recorded Koszul complex.
* `koszulDualCochainComplex`: its extension by zero to integer degrees.

## References

* [Stacks, Tag 0BQZ]
-/

@[expose] public section

universe uD

open CategoryTheory

namespace ExteriorAlgebra

/-- The total Hom differential in degree `n`, with the Stacks total Hom sign. -/
noncomputable def koszulDualBoundary (A : Type uD) [CommRing A] (r n : ℕ) (f : Fin r → A) :
    ((koszulComplex A r f).X n ⟶ ModuleCat.of A A) →ₗ[A]
      ((koszulComplex A r f).X (n + 1) ⟶ ModuleCat.of A A) :=
  (-1 : A) ^ (n + 1) •
    Linear.leftComp A (ModuleCat.of A A) ((koszulComplex A r f).d (n + 1) n)

/-- The signed precomposition differentials have square zero. -/
theorem koszulDualBoundary_comp (A : Type uD) [CommRing A] (r : ℕ) (f : Fin r → A)
    (n : ℕ) :
    ModuleCat.ofHom (koszulDualBoundary A r n f) ≫
      ModuleCat.ofHom (koszulDualBoundary A r (n + 1) f) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((koszulDualBoundary A r (n + 1) f) (koszulDualBoundary A r n f x)) = 0
  simp [koszulDualBoundary, Linear.leftComp]

/-- `Hom_A^•(K_A(f), A)`, indexed in nonnegative cohomological degrees.
Its differential is `x ↦ (-1)^(n+1) x ∘ d_{n+1}`. -/
noncomputable def koszulDualComplex (A : Type uD) [CommRing A] (r : ℕ) (f : Fin r → A) :
    CochainComplex (ModuleCat.{uD} A) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of A ((koszulComplex A r f).X n ⟶ ModuleCat.of A A))
    (fun n ↦ ModuleCat.ofHom (koszulDualBoundary A r n f))
    (koszulDualBoundary_comp A r f)

end ExteriorAlgebra

namespace ExteriorAlgebra

/-- The integer-indexed total dual complex, with zero terms in negative degrees. -/
noncomputable def koszulDualCochainComplex (A : Type uD) [CommRing A] (r : ℕ)
    (f : Fin r → A) : CochainComplex (ModuleCat.{uD} A) ℤ :=
  (koszulDualComplex A r f).extend ComplexShape.embeddingUpNat

end ExteriorAlgebra
