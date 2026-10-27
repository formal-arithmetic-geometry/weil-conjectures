module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField

/-! # Weights of a finite projective module under a split torus

Source: Conrad, Reductive Group Schemes, Proposition 3.1.9 proof (1), pp.86--87,
and Lemma 2.2.4 proof, p.66. The affine module formulation includes arbitrary base
change and the zero ring. (blueprint: lem-sfb-relative-torus-bundle-weights)
-/

set_option autoImplicit false

@[expose] public section

universe u v w

open scoped TensorProduct DirectSum

namespace SplitTorus

variable {A : Type u} [CommRing A] {V : Type v} [AddCommGroup V] [Module A V]
variable {M : Type w} [AddCommGroup M]

/-- The character submodule: the kernel of `rho - (v ↦ v tensor e^m)`.
Source: Conrad, Proposition 3.1.9 proof (1), p.86.
(blueprint: lem-sfb-relative-torus-bundle-weights) -/
noncomputable def weightSpace (ρ : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A M) (m : M) :
    Submodule A V :=
  (ρ - (TensorProduct.mk A V (AddMonoidAlgebra A M)).flip
    (AddMonoidAlgebra.single m 1)).ker

/-- Scalar extension of the coaction, using the canonical tensor distribution and
`S tensor A[M] = S[M]`. We write the new scalar factor first; tensor symmetry
identifies this with `V tensor S` in the source.
Source: Conrad, Proposition 3.1.9 proof (1), p.86.
(blueprint: lem-sfb-relative-torus-bundle-weights) -/
noncomputable def baseChangeCoaction (S : Type*) [CommRing S] [Algebra A S]
    (ρ : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A M) :
    S ⊗[A] V →ₗ[S] (S ⊗[A] V) ⊗[S] AddMonoidAlgebra S M :=
  TensorProduct.map LinearMap.id (AddMonoidAlgebra.scalarTensorEquiv A S).toLinearMap ∘ₗ
    (TensorProduct.AlgebraTensorModule.distribBaseChange A S V
      (AddMonoidAlgebra A M)).toLinearMap ∘ₗ ρ.baseChange S

/-- Restriction along the quotient Hopf map `e^m ↦ e^(m mod L)`.
Source: Conrad, Proposition 3.1.9 proof (1), pp.86--87.
(blueprint: lem-sfb-relative-torus-bundle-weights) -/
noncomputable def restrictCoaction (ρ : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A M)
    (L : AddSubgroup M) : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A (M ⧸ L) :=
  (AddMonoidAlgebra.mapDomainLinearMap A A (QuotientAddGroup.mk' L)).lTensor V ∘ₗ ρ

/-- Invariants for the subgroup `Spec A[M/L]`, as the zero-character submodule
of the restricted coaction, rather than invariants of the group of A-points.
Source: Conrad, Lemma 2.2.4 proof, p.66, and Proposition 3.1.9 proof (1), p.87.
(blueprint: lem-sfb-relative-torus-bundle-weights) -/
noncomputable def invariants (ρ : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A M)
    (L : AddSubgroup M) : Submodule A V :=
  weightSpace (restrictCoaction ρ L) 0

open Classical in
/-- The natural sum of character inclusions indexed by a subgroup of the character lattice.
Source: Conrad, Proposition 3.1.9 proof (1), p.87.
(blueprint: lem-sfb-relative-torus-bundle-weights) -/
noncomputable def subgroupSum (ρ : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A M)
    (L : AddSubgroup M) : (⨁ m : L, weightSpace ρ (m : M)) →ₗ[A] V :=
  DirectSum.toModule A L V (fun m ↦ (weightSpace ρ (m : M)).subtype)

/-- The affine residue-field dimension of a character fibre. The field
`p.asIdeal.ResidueField` is canonically the recorded scheme residue field via
`AlgebraicGeometry.Scheme.Spec.residueFieldIso`; see also
`AlgebraicGeometry.spec_field_point_residue_field`.
Source: Conrad, Proposition 3.1.9 proof (1), p.86; Stacks Tag 00NX.
(blueprint: lem-sfb-relative-torus-bundle-weights) -/
noncomputable def fibreDimension (ρ : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A M)
    (m : M) (p : PrimeSpectrum A) : ℕ :=
  Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] weightSpace ρ m)

open Classical in
/-- Weight decomposition, finite projectivity, and simultaneous local constancy.
Source: Conrad, Proposition 3.1.9 proof (1), pp.86--87; Lemma 2.2.4 proof, p.66;
Stacks Tag 00NX. (blueprint: lem-sfb-relative-torus-bundle-weights)

Proof: (1) Coefficient extraction identifies W tensor A[M] with finitely supported
families in W, and likewise for two group-algebra factors. (2) Write p_m for the
m-th coefficient of rho; coassociativity makes p_m(v) a weight-m vector, while
counitality gives v = sum p_m(v), and p_m is delta_mn on V_n. (3) These maps
therefore invert the direct-sum inclusion. (4) A finite-free retraction of V gives
finitely many generators; the union of their finite coefficient supports contains
all nonzero weights. (5) Each p_m splits the inclusion of V_m, so every V_m is a
direct summand of a finite free module. (6) After A to A' use the canonical
isomorphism A' tensor A[M] = A'[M]; the coefficient projector is p_m tensor 1,
and its split inclusion identifies the new weight space with the base-changed one.
(7) Applying the quotient Hopf map e^m maps to e^(m mod L), coefficient comparison
shows that invariants are exactly the direct sum of the weights in L; tensoring the
same splitting gives the invariant base-change clause. (8) Apply
Module.isLocallyConstant_rankAtStalk to the finitely many finite-projective weight
modules. The residue-field identification from lem-weil-pbc-spec-field-point-residue-field
identifies those ranks with fibreDimension; intersect their open neighborhoods.
Weights outside the finite support are zero. Empty support uses the whole spectrum,
and the zero ring has no points.
-/
theorem relative_torus_bundle_weights
    (r : ℕ) (ρ : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A (Fin r → ℤ))
    [Module.Finite A V] [Module.Projective A V]
    (hcoassoc : (TensorProduct.assoc A V _ _).toLinearMap ∘ₗ ρ.rTensor _ ∘ₗ ρ =
      (Coalgebra.comul (R := A) (A := AddMonoidAlgebra A (Fin r → ℤ))).lTensor V ∘ₗ ρ)
    (hcounit : (TensorProduct.rid A V).toLinearMap ∘ₗ
      (Coalgebra.counit (R := A) (A := AddMonoidAlgebra A (Fin r → ℤ))).lTensor V ∘ₗ ρ =
        LinearMap.id) :
    Function.Bijective (DirectSum.coeLinearMap (weightSpace ρ)) ∧
    Set.Finite {m : Fin r → ℤ | weightSpace ρ m ≠ ⊥} ∧
    (∀ m : Fin r → ℤ, Module.Finite A (weightSpace ρ m) ∧
      Module.Projective A (weightSpace ρ m)) ∧
    ∀ s : PrimeSpectrum A, ∃ U : TopologicalSpace.Opens (PrimeSpectrum A), s ∈ U ∧
      ∀ p ∈ U, ∀ m : Fin r → ℤ, fibreDimension ρ m p = fibreDimension ρ m s := by
  sorry

/-- Weight formation commutes with every ring map, including nonflat base change;
the natural tensor inclusions are injective and have exactly the new weight spaces as images.
Source: Conrad, Proposition 3.1.9 proof (1), p.86.
(blueprint: lem-sfb-relative-torus-bundle-weights)

Proof: step (6). Tensor each weight-inclusion retraction from the coefficient proof.
Its tensor is still a left inverse, so the natural inclusion remains injective.
The new coefficient projector on s tensor v is s tensor p_m(v), by the formula
for baseChangeCoaction. Its image is both the new weight space and the image of
the tensor inclusion, proving the claimed equality inside S tensor V.
-/
theorem relative_torus_bundle_weights_baseChange
    (r : ℕ) (ρ : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A (Fin r → ℤ))
    [Module.Finite A V] [Module.Projective A V]
    (hcoassoc : (TensorProduct.assoc A V _ _).toLinearMap ∘ₗ ρ.rTensor _ ∘ₗ ρ =
      (Coalgebra.comul (R := A) (A := AddMonoidAlgebra A (Fin r → ℤ))).lTensor V ∘ₗ ρ)
    (hcounit : (TensorProduct.rid A V).toLinearMap ∘ₗ
      (Coalgebra.counit (R := A) (A := AddMonoidAlgebra A (Fin r → ℤ))).lTensor V ∘ₗ ρ =
        LinearMap.id)
    (S : Type w) [CommRing S] [Algebra A S] (m : Fin r → ℤ) :
    Function.Injective ((weightSpace ρ m).subtype.baseChange S) ∧
      (weightSpace ρ m).baseChange S = weightSpace (baseChangeCoaction S ρ) m := by
  sorry

open Classical in
/-- Restriction to a quotient-character subtorus has the sum of the L-weights as
its invariant module. Injectivity and the stated image identify the natural sum
with that invariant module.
Source: Conrad, Proposition 3.1.9 proof (1), pp.86--87; Lemma 2.2.4 proof, p.66.
(blueprint: lem-sfb-relative-torus-bundle-weights)

Proof: step (7). Apply the quotient Hopf map to the finite weight expansion of v.
For each nonzero quotient character the sum of the corresponding weight components
must vanish if v is invariant. Apply each original coefficient projector p_n to
this equality to see that every component outside L vanishes. Conversely each
L-component maps to the zero quotient character and is invariant. The original
weight decomposition makes the subgroup sum injective, with precisely this image.
-/
theorem relative_torus_bundle_weights_invariants
    (r : ℕ) (ρ : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A (Fin r → ℤ))
    [Module.Finite A V] [Module.Projective A V]
    (hcoassoc : (TensorProduct.assoc A V _ _).toLinearMap ∘ₗ ρ.rTensor _ ∘ₗ ρ =
      (Coalgebra.comul (R := A) (A := AddMonoidAlgebra A (Fin r → ℤ))).lTensor V ∘ₗ ρ)
    (hcounit : (TensorProduct.rid A V).toLinearMap ∘ₗ
      (Coalgebra.counit (R := A) (A := AddMonoidAlgebra A (Fin r → ℤ))).lTensor V ∘ₗ ρ =
        LinearMap.id)
    (L : AddSubgroup (Fin r → ℤ)) [Module.Free ℤ ((Fin r → ℤ) ⧸ L)] :
    Function.Injective (subgroupSum ρ L) ∧ (subgroupSum ρ L).range = invariants ρ L := by
  sorry

/-- Arbitrary base change also preserves the invariant module for the restricted action,
with its natural inclusion.
Source: Conrad, Lemma 2.2.4 proof, p.66, and Proposition 3.1.9 proof (1), p.87.
(blueprint: lem-sfb-relative-torus-bundle-weights)

Proof: the last part of step (7). The finite sum of the coefficient projectors
indexed by L is a retraction onto the invariant module. Tensoring this retraction
proves injectivity of its natural tensor inclusion. Step (6) identifies the
base-changed weight summands. Summing those indexed by L gives exactly the
invariants of the restricted extended coaction by the coefficient argument above.
Thus the equality is under the canonical inclusions for every A-algebra S.
-/
theorem relative_torus_bundle_weights_invariants_baseChange
    (r : ℕ) (ρ : V →ₗ[A] V ⊗[A] AddMonoidAlgebra A (Fin r → ℤ))
    [Module.Finite A V] [Module.Projective A V]
    (hcoassoc : (TensorProduct.assoc A V _ _).toLinearMap ∘ₗ ρ.rTensor _ ∘ₗ ρ =
      (Coalgebra.comul (R := A) (A := AddMonoidAlgebra A (Fin r → ℤ))).lTensor V ∘ₗ ρ)
    (hcounit : (TensorProduct.rid A V).toLinearMap ∘ₗ
      (Coalgebra.counit (R := A) (A := AddMonoidAlgebra A (Fin r → ℤ))).lTensor V ∘ₗ ρ =
        LinearMap.id)
    (L : AddSubgroup (Fin r → ℤ)) [Module.Free ℤ ((Fin r → ℤ) ⧸ L)]
    (S : Type w) [CommRing S] [Algebra A S] :
    Function.Injective ((invariants ρ L).subtype.baseChange S) ∧
      (invariants ρ L).baseChange S = invariants (baseChangeCoaction S ρ) L := by
  sorry

end SplitTorus
