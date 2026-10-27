module

public import Sheaf.AlgebraicGeometry.GroupScheme.RingRationalModule
public import Sheaf.AlgebraicGeometry.GroupScheme.RingSplitSemisimple
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded

/-! # A primitive fixed vector has a scalar endomorphism detector

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Lemmas 9.7.2 and 9.7.4, Remark 9.7.3 and Theorem 9.7.5, pp.526--528.
(blueprint: lem-sfb-dvr-primitive-endomorphism-detector)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A primitive invariant vector admits an equivariant endomorphism detector with
scalar invariant endomorphisms and nonzero residue. The witness W is written in a
finite basis as Fin n → A; n > 0 is precisely positive rank. The displayed identity
for phi says that evaluation V tensor W → W is equivariant, equivalently that phi
is equivariant for conjugation on End(W). The equivalence e is pinned to the scalar
map on every element, so the assertion concerns the canonical scalar map.

Source: Alper, Lemmas 9.7.2(1),(2), 9.7.4, Remark 9.7.3 and Theorem 9.7.5,
pp.526--528 (blueprint: lem-sfb-dvr-primitive-endomorphism-detector).

Proof plan:
1. Choose a split torus and Borel. By lem-sfb-dvr-rho-section-modules choose rho,
its extension, and the actual positive-rank finite free left-translation modules W_m.
2. By lem-sfb-dvr-rho-tensor-square-eventual-detection choose a threshold M for V,v.
In residue characteristic zero use m=M. In characteristic p>0 choose r>=1 with
p^r-1>=M and use m=p^r-1. Apply lem-sfb-dvr-rho-section-self-duality at this same m
for an equivariant j:W_m ≃ W_m dual. Detection gives a:V → W_m tensor W_m,
nonzero at v after reduction.
3. Send w tensor ell to (z ↦ ell(z)w). Its inverse sends T to the finite sum
of T(e_i) tensor e_i dual. Basis expansion proves both inverse identities. They
remain inverse after residue extension. The formula commutes with the diagonal
and conjugation actions, so composing a with 1 tensor j and this map gives phi.
Its residual value is nonzero under the canonical matrix base-change identification.
4. By lem-sfb-dvr-rho-tensor-square-invariant-line the tensor-square invariants are
free of rank one. The equivariant isomorphism and inverse identify this module with
the invariant endomorphisms N.
5. Choose a generator T of N and write id=bT. A diagonal entry exists since W has
positive rank, and gives 1=bT_ii. Thus b is a unit, every invariant endomorphism
is scalar, and a scalar annihilating id is zero by a diagonal entry. The scalar
map is therefore a linear isomorphism. Choose a finite basis of W to present it
as Fin n → A and transport the coaction, map and all conclusions along that basis.
-/
theorem dvr_primitive_endomorphism_detector
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (H : Grp (Over (Spec (.of A))))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (hH : RingSemisimple.IsSplitSemisimpleSimplyConnected H)
    (V : Type v) [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
    (ρ : RingRational.Coaction A Γ(H.X.left, ⊤) V) (v : V)
    (hv : ρ.map v = v ⊗ₜ[A] (1 : Γ(H.X.left, ⊤)))
    (hprimitive : v ∉ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A V)) :
    ∃ (n : ℕ) (_ : 0 < n)
      (σ : RingRational.Coaction A Γ(H.X.left, ⊤) (Fin n → A))
      (φ : V →ₗ[A] Module.End A (Fin n → A)),
      (∀ (x : V) (w : Fin n → A),
        RingRational.evaluateTensor (φ.rTensor Γ(H.X.left, ⊤) (ρ.map x)) (σ.map w) =
          σ.map (φ x w)) ∧
      (∃ e : A ≃ₗ[A] RingRational.invariantEnd σ,
        ∀ a : A, (e a).val = a • LinearMap.id) ∧
      (φ v).baseChange (IsLocalRing.ResidueField A) ≠ 0 := by
  sorry

end AlgebraicGeometry
