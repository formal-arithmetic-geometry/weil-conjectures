module

public import Sheaf.AlgebraicGeometry.InfinitesimalRegularCochains
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.RingTheory.Kaehler.TensorProduct
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic

/-! # The regular multiplicativity defect of a square-zero homomorphism lift

Source: Conrad, Reductive group schemes, Proposition B.2.5 and Corollary B.2.6,
printed pp.286--287 (blueprint: lem-sfb-square-zero-hom-regular-defect).

Affine schemes are expressed through their coordinate Hopf algebras. Mathlib's
`Spec.mapMulEquiv` identifies their convolution groups with scheme-valued points.
Tensor reduction and J/J² are the canonical presentations of R/JR and J.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory TensorProduct Coalgebra Bialgebra WithConv
open scoped TensorProduct

namespace AlgebraicGeometry.InfinitesimalRegular

/-- The kernel comparison, its regular adjoint action, and the regular defect and correction.
Source: Conrad B.2.5--B.2.6, pp.286--287
(blueprint: lem-sfb-square-zero-hom-regular-defect).

Proof:
1. Smooth relative differentials are finite locally free; pull back to the identity.
Differential base change and finite locally free affine sections make P finite projective
(lem-ag-smooth-relative-differentials-finite-locally-free, def-pc-module-pullback,
lem-weil-pbc-kahler-differentials-base-change, lem-pc-finite-flat-affine-sections-projective).
2. A finite dual basis identifies Hom(P,N) with P-dual tensor N, naturally in N
(def-weil-pbc-projective-module). This includes rank zero.
3. Flatness identifies J tensor R with JR; square zero balances this tensor over A/J
(lem-trf-flat-tensor-preserves-injection). Tensor powers of C are flat, and their
reductions are the corresponding tensor powers of C/JC.
4. The square-zero kernel module and the affine module correspondence identify the
kernel with Hom(P,JR), hence with E tensor R0. The coordinate map is epsilon plus the
associated derivation, giving the normalization below and naturality
(lem-sfb-group-space-square-zero-kernel-module,
lem-sfb-space-affine-module-correspondence, lem-sfb-space-square-zero-lift-linearization).
5. Differentiate conjugation at the universal point of G0. Transpose on P and tensor
with J, then substitute u0, obtaining the counital coassociative regular coaction
(def-weil-pbc-kahler-differentials, lem-sfb-space-square-zero-lift-linearization).
6. For a kernel derivation D, conjugation has coordinate difference
sum g(a1) D(a2) g-inverse(a3). Since D lands in JR, the outer factors reduce modulo JR.
This proves compatibility with the displayed coaction, without choosing lifts.
7. At the universal pair over C tensor C the defect lies in the kernel. Its inverse
image under kappa is the unique regular tensor c. Flatness and naturality give its
formula at every flat test algebra (def-weil-affine-spectrum, def-pc-fibre-product).
8. Compute f((hk)l) and f(h(kl)); cancel f(h)f(k)f(l). The abelian kernel and step 6
turn this into the displayed cocycle identity. The universal triple detects equality
in the regular degree-three cochain module. No identity normalization is used.
9. The C-point kappa_C(b) is an actual morphism H to G reducing to the identity section.
Multiplying it with f gives the coordinate map correct below (def-weil-affine-spectrum).
10. Expand the new defect: beta(hk) d(h,k) (f(h) beta(k)^(-1) f(h)^(-1)) beta(h)^(-1).
The additive kernel formula is c + b(hk) - h.b(k) - b(h), with the stated minus sign.
Universality makes this an equality of regular tensors.
11. At the universal pair, c=0 iff its multiplicative defect is 1 iff the two
multiplication coordinate maps agree (def-weil-affine-spectrum). This is exactly the
scheme-morphism equality f composed with m_H = m_G composed with (f times f).
-/
theorem squareZeroHom_regularDefect
    (A D C : Type u) [CommRing A] [CommRing D] [CommRing C]
    [HopfAlgebra A D] [HopfAlgebra A C] (J : Ideal A) (hJ : J ^ 2 = ⊥)
    [Module.Flat A C]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap A D)))]
    (u₀ : Reduced A J D →ₐc[A ⧸ J] Reduced A J C)
    (f : D →ₐ[A] C) (hf : reduceMap A J f = u₀.toAlgHom) :
    ∃ (κ : Comparison A J D)
      (ρ : Coeff A J D →ₗ[A ⧸ J] Coeff A J D ⊗[A ⧸ J] Reduced A J C),
      IsCoaction ρ ∧
      (∀ (R : Type u) [CommRing R] [Algebra A R] [Module.Flat A R]
        (v w : Coeff A J D ⊗[A ⧸ J] Reduced A J R),
        (κ R (v + w)).val = (κ R v).val * (κ R w).val) ∧
      (∀ (R : Type u) [CommRing R] [Algebra A R] [Module.Flat A R]
        (φ : Module.Dual (A ⧸ J) (identityCotangent (A ⧸ J) (Reduced A J D)))
        (j : J) (r : R) (d : D) (a : A),
        Ideal.Quotient.mk J a =
            φ (identityDifferential (A ⧸ J) (Reduced A J D) (reduce A J D d)) →
        ((κ R ((φ ⊗ₜ[A ⧸ J] J.toCotangent j) ⊗ₜ[A ⧸ J] reduce A J R r)).val.ofConv d) =
          algebraMap A R (counitAlgHom A D d) + algebraMap A R (a * (j : A)) * r) ∧
      (∀ (R T : Type u) [CommRing R] [CommRing T] [Algebra A R] [Algebra A T]
        [Module.Flat A R] [Module.Flat A T] (α : R →ₐ[A] T)
        (v : Coeff A J D ⊗[A ⧸ J] Reduced A J R),
        (κ T (TensorProduct.map LinearMap.id (reduceMap A J α).toLinearMap v)).val =
          toConv (α.comp (κ R v).val.ofConv)) ∧
      (∀ (R : Type u) [CommRing R] [Algebra A R] [Module.Flat A R]
          (h : WithConv (C →ₐ[A] R)) (v : Coeff A J D ⊗[A ⧸ J] Reduced A J R),
          (κ R (action ρ (reduceMap A J h.ofConv) v)).val =
            toConv (h.ofConv.comp f) * (κ R v).val * inverse (toConv (h.ofConv.comp f))) ∧
        ∃ c : Cochain (K := A ⧸ J) (Reduced A J C) (Coeff A J D) 2,
          HasDefect A J κ f c ∧
          (∀ c', HasDefect A J κ f c' → c' = c) ∧
          (∀ (T : Type u) [CommRing T] [Algebra (A ⧸ J) T]
            (h k l : WithConv (Reduced A J C →ₐ[A ⧸ J] T)),
            action ρ h.ofConv (eval ![k.ofConv, l.ofConv] c) -
              eval ![(h * k).ofConv, l.ofConv] c +
              eval ![h.ofConv, (k * l).ofConv] c - eval ![h.ofConv, k.ofConv] c = 0) ∧
          (∀ b : Coeff A J D ⊗[A ⧸ J] Reduced A J C,
            reduceMap A J (correct A J κ f b) = u₀.toAlgHom ∧
            ∃ c_b : Cochain (K := A ⧸ J) (Reduced A J C) (Coeff A J D) 2,
              HasDefect A J κ (correct A J κ f b) c_b ∧
              ∀ (T : Type u) [CommRing T] [Algebra (A ⧸ J) T]
                (h k : WithConv (Reduced A J C →ₐ[A ⧸ J] T)),
                eval ![h.ofConv, k.ofConv] c_b = eval ![h.ofConv, k.ofConv] c -
                  (action ρ h.ofConv (TensorProduct.map LinearMap.id k.ofConv.toLinearMap b) -
                    TensorProduct.map LinearMap.id (h * k).ofConv.toLinearMap b +
                    TensorProduct.map LinearMap.id h.ofConv.toLinearMap b)) ∧
          (c = 0 ↔ (comulAlgHom A C).comp f =
            (Algebra.TensorProduct.map f f).comp (comulAlgHom A D)) := by
  sorry

end AlgebraicGeometry.InfinitesimalRegular
