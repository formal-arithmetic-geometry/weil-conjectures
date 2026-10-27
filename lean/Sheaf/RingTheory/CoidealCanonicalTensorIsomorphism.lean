module

public import Sheaf.RingTheory.RelativeHopfModuleKernels

/-! # The canonical tensor isomorphism for a right coideal subalgebra

Source: Bichon, arXiv:2301.05480v2, section 2.2, Proposition 2.2 and its displayed inverse.
(blueprint: lem-sfb-coideal-canonical-tensor-isomorphism)

The structure records the specified diagonal action, coactions and both generator formulas.
Its existence theorem also states naturality for arbitrary H-linear maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open scoped TensorProduct

namespace RelativeHopf

variable (k : Type u) [Field k] (H : Type v) [CommRing H] [Bialgebra k H]
variable (A : Subalgebra k H) [hJ : ((augmentationIdeal k H A).restrictScalars k).IsCoideal]
variable (S : H →ₐ[k] H)
variable (X : Type w) [AddCommGroup X] [Module H X] [Module A X] [Module k X]
variable [IsScalarTower A H X] [IsScalarTower k A X] [IsScalarTower k H X]

/-- The canonical isomorphism, with all its specified structures and generator formulas.
The compatible A-action on X is its restriction from H, as expressed by the scalar tower.
The instance fields package the diagonal module structure without choosing an arbitrary map.
Source: Bichon, Proposition 2.2 and its inverse formula.
(blueprint: lem-sfb-coideal-canonical-tensor-isomorphism) -/
structure CanonicalTensorIsomorphism where
  /-- The diagonal H-module structure on C tensor X. -/
  [diagonalModule : Module H (Quotient k H A ⊗[k] X)]
  /-- Its scalar restriction agrees with the given k-module structure. -/
  [diagonalTower : @IsScalarTower k H (Quotient k H A ⊗[k] X)
    _ diagonalModule.toSMul _]
  /-- The action is exactly the one induced by Delta. -/
  diagonal_smul : ∀ (h : H) (z : Quotient k H A ⊗[k] X),
    @SMul.smul H (Quotient k H A ⊗[k] X) diagonalModule.toSMul h z =
      tensorAction k H (Quotient k H A) X (Coalgebra.comul h) z
  /-- The coaction on the induced module. -/
  induced : Coaction k H (Quotient k H A) (H ⊗[A] X)
  /-- It is the canonical induced coaction of the dependency. -/
  induced_formula : IsInduced k H A X induced
  /-- The relative coaction on the diagonal tensor module. -/
  coaction : @Coaction k _ H _ _ (Quotient k H A) _ _ _ _
    (Quotient k H A ⊗[k] X) _ _ diagonalModule diagonalTower _
  /-- Its underlying map is Delta_C tensor 1, followed by the associator. -/
  coaction_formula : coaction.map =
    (TensorProduct.assoc k (Quotient k H A) (Quotient k H A) X).toLinearMap ∘ₗ
      (Coalgebra.comul (R := k) (A := Quotient k H A)).rTensor X
  /-- The H-linear equivalence kappa. -/
  equiv : (H ⊗[A] X) ≃ₗ[H] (Quotient k H A ⊗[k] X)
  /-- The forward map on h tensor x is pi(h_1) tensor h_2 x. -/
  forward_formula : ∀ (h : H) (x : X), equiv (h ⊗ₜ[A] x) =
    TensorProduct.map (quotientMap k H A)
      ((Algebra.lsmul k k X).toLinearMap.flip x) (Coalgebra.comul h)
  /-- The inverse on pi(h) tensor x is h_1 tensor S(h_2)x. -/
  inverse_formula : ∀ (h : H) (x : X) (n : ℕ) (a b : Fin n → H),
    Coalgebra.comul (R := k) h = ∑ i, a i ⊗ₜ[k] b i →
    equiv.symm (quotientMap k H A h ⊗ₜ[k] x) = ∑ i, a i ⊗ₜ[A] (S (b i) • x)
  /-- The forward equivalence commutes with coactions. -/
  hom_isMorphism : IsMorphism k H (Quotient k H A) (H ⊗[A] X)
    (Quotient k H A ⊗[k] X) induced coaction equiv.toLinearMap
  /-- The inverse equivalence commutes with coactions. -/
  inv_isMorphism : IsMorphism k H (Quotient k H A) (Quotient k H A ⊗[k] X)
    (H ⊗[A] X) coaction induced equiv.symm.toLinearMap

omit hJ in
/-- The canonical tensor equivalences exist and are natural for H-linear maps.
Source: Bichon, arXiv:2301.05480v2, section 2.2, Proposition 2.2.
(blueprint: lem-sfb-coideal-canonical-tensor-isomorphism)

Proof plan (the eight steps of the node):
1. Use lem-sfb-relative-hopf-module-kernels to obtain pi(ta) = epsilon(a)pi(t).
   Its quotient coalgebra identities show that C is an H-module coalgebra.
2. Multiplicativity of Delta makes the displayed diagonal action associative and unital.
   Coassociativity and the counit on C give the coaction axioms for Delta_C tensor 1;
   the H-module coalgebra identity gives relative compatibility.
3. Expand Delta(a) in A tensor H. The quotient identity and counit make the forward
   expression A-balanced. The tensor universal property
   (def-weil-pbc-module-tensor-product) gives kappa, and multiplicativity gives H-linearity.
4. For G(h,x) = sum h_1 tensor S(h_2)x, balancing and the antipode identity give
   G(ha,x) = epsilon(a)G(h,x). It vanishes on HA-plus, so descends through pi,
   then through the k-tensor product, giving the stated inverse formula.
5. Coassociativity and mu(S tensor 1)Delta = eta epsilon give lambda kappa = 1
   on generating tensors h tensor_A x.
6. The other antipode identity gives kappa lambda = 1 on pi(h) tensor x;
   surjectivity of pi and tensor generation extend this to all elements.
7. Coassociativity proves the forward coaction square on generators. Its inverse
   is H-linear and colinear by composing the square with the inverse maps.
8. For H-linear f, f(h_2 x) = h_2 f(x) proves the naturality square on generators.
   Both tensor maps commute with the actions and coactions by the same formulas.
No antipode stability of A or flatness assumption is used. -/
theorem coidealCanonicalTensorIsomorphism (hA : IsRightCoideal k H A)
    (hSleft : LinearMap.mul' k H ∘ₗ S.toLinearMap.rTensor H ∘ₗ Coalgebra.comul =
      Algebra.linearMap k H ∘ₗ Coalgebra.counit)
    (hSright : LinearMap.mul' k H ∘ₗ S.toLinearMap.lTensor H ∘ₗ Coalgebra.comul =
      Algebra.linearMap k H ∘ₗ Coalgebra.counit) :
    ∃ hJ : ((augmentationIdeal k H A).restrictScalars k).IsCoideal,
    (∀ (X : Type w) [AddCommGroup X] [Module H X] [Module A X] [Module k X]
      [IsScalarTower A H X] [IsScalarTower k A X] [IsScalarTower k H X],
      Nonempty (CanonicalTensorIsomorphism k H A S X (hJ := hJ))) ∧
    (∀ (X : Type w) [AddCommGroup X] [Module H X] [Module A X] [Module k X]
      [IsScalarTower A H X] [IsScalarTower k A X] [IsScalarTower k H X]
      (Y : Type w') [AddCommGroup Y] [Module H Y] [Module A Y] [Module k Y]
      [IsScalarTower A H Y] [IsScalarTower k A Y] [IsScalarTower k H Y]
      (eX : CanonicalTensorIsomorphism k H A S X (hJ := hJ))
      (eY : CanonicalTensorIsomorphism k H A S Y (hJ := hJ)) (f : X →ₗ[H] Y) (h : H) (x : X),
      (f.restrictScalars k).lTensor (Quotient k H A) (eX.equiv (h ⊗ₜ[A] x)) =
        eY.equiv (h ⊗ₜ[A] f x)) := by
  sorry

end RelativeHopf
