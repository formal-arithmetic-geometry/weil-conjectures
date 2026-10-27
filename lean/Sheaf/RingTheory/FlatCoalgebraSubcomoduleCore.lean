module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# The stable core of a submodule of a flat coalgebra comodule

Source: Milne, Basic Theory of Affine Group Schemes (2012), VIII, Aside 4.7,
printed p.117, stable-core argument before finite generation
(blueprint: lem-sfb-flat-coalgebra-subcomodule-core).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Coalgebra

/-- The stable core of `W` is a submodule contained in `W`, has a unique restricted
coaction, and contains every stable submodule of `W`.
Source: Milne, Basic Theory of Affine Group Schemes (2012), VIII, Aside 4.7, p.117
(blueprint: lem-sfb-flat-coalgebra-subcomodule-core).

Proof plan:
1. The inverse image of the tensor-inclusion range is a submodule. Applying the
counit to a tensor expression with coefficients in `W` shows that this core lies in `W`.
2. For the quotient map `q : M → M/W`, tensor right exactness identifies the core
with the kernel of `f = (q ⊗ 1)ρ` (lem-weil-pbc-tensor-right-exact).
3. Coassociativity gives `(f ⊗ 1)ρ = (1 ⊗ Δ)f`, so it vanishes on the core.
Flat tensor exactness identifies the image of `K ⊗ C → M ⊗ C` with the kernel of
`f ⊗ 1` and makes this inclusion injective (lem-weil-pbc-flat-tensor-exact).
Thus `ρ` restricts uniquely to an R-linear coaction on `K`.
4. Postcompose the counit identity with `K → M` and the coassociativity identity
with `(K ⊗ C) ⊗ C → (M ⊗ C) ⊗ C`. These maps are injective, the latter by
flatness twice, and the identities reduce to those for `ρ`.
5. If `U ≤ W` is stable, tensor functoriality places its coaction in the tensor
range of `W`, so every element of `U` belongs to the core. -/
theorem flat_subcomodule_core
    {R : Type u} [CommRing R] {C : Type v} [AddCommGroup C] [Module R C]
    [Coalgebra R C] [Module.Flat R C]
    {M : Type w} [AddCommGroup M] [Module R M]
    (ρ : M →ₗ[R] M ⊗[R] C)
    (hρassoc : (TensorProduct.assoc R M C C).toLinearMap ∘ₗ ρ.rTensor C ∘ₗ ρ =
      (Coalgebra.comul (R := R) (A := C)).lTensor M ∘ₗ ρ)
    (hρcounit : (TensorProduct.rid R M).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := C)).lTensor M ∘ₗ ρ = LinearMap.id)
    (W K : Submodule R M)
    (hK : K = (LinearMap.range (W.subtype.rTensor C)).comap ρ) :
    K ≤ W ∧
      (∃ ρK : K →ₗ[R] K ⊗[R] C,
        K.subtype.rTensor C ∘ₗ ρK = ρ ∘ₗ K.subtype ∧
        (TensorProduct.assoc R K C C).toLinearMap ∘ₗ ρK.rTensor C ∘ₗ ρK =
          (Coalgebra.comul (R := R) (A := C)).lTensor K ∘ₗ ρK ∧
        (TensorProduct.rid R K).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := C)).lTensor K ∘ₗ ρK = LinearMap.id ∧
        ∀ ρK' : K →ₗ[R] K ⊗[R] C,
          K.subtype.rTensor C ∘ₗ ρK' = ρ ∘ₗ K.subtype → ρK' = ρK) ∧
      ∀ U : Submodule R M, U ≤ W →
        U ≤ (LinearMap.range (U.subtype.rTensor C)).comap ρ → U ≤ K := by
  sorry

end Coalgebra
