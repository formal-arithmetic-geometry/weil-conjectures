module

public import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.RingTheory.TensorProduct.Maps

import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Yoneda
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # The unit torus and its embedding-indexed character basis

Source: Milne, Algebraic Groups (2017), Sections 2.54--2.61, pp.57--59,
and Lemma 12.61, p.251 (blueprint: lem-sfb-induced-unit-torus-characters).

The representing group is specified on every commutative test algebra, naturally.
The character normalization is tested on every algebra over the separable closure,
so it identifies scheme characters, including over nonreduced rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.MultiplicativeType

/-- The units of a finite separable extension are represented by an affine torus
of finite type. Its characters have the embedding-indexed permutation basis.

Source: Milne, Sections 2.54--2.61, pp.57--59, Proposition 12.60, p.250,
and Lemma 12.61, p.251 (blueprint: lem-sfb-induced-unit-torus-characters).

Proof plan:
1. Choose a finite basis of L. The finite-algebra units affine chart
   (lem-sfb-finite-algebra-units-affine-chart) represents units by D(N).
   Use lem-weil-pbc-affine-open-section-vanishing-prime to identify D(N)
   with Spec of the localization. The localization-away polynomial quotient
   gives finite generation; affine schemes are quasi-compact, hence finite type.
2. Transport multiplication, identity and inverse from units. Affine fibre
   products and lem-galois-yoneda-fully-faithful turn these natural operations
   and their identities into a group scheme, giving the natural group isomorphisms.
3. Finite dimensionality makes each element algebraic. Distinct minimal-polynomial
   roots imply coprimality with the derivative, hence separability. Apply
   lem-zl-finite-separable-tensor-primitive-presentation and separable polynomial
   linear factorization over ks; the roots are distinct by the Bezout identity.
4. The ideals of distinct roots are pairwise comaximal. Apply the Chinese
   remainder isomorphism and evaluation, and identify roots with embeddings by
   the minimal-polynomial quotient and polynomial-quotient Hom equivalence.
   This gives theta with the displayed pure-tensor formula.
5. Tensor associativity and lem-weil-pbc-tensor-finite-product extend this
   decomposition to every ks-algebra. Taking units splits the base-changed group
   as a product of G_m; extending to the algebraic closure proves it is a torus.
6. By lem-sfb-split-torus-hom-matrices, each character is uniquely a product of
   integer powers of coordinate characters. This gives chi, preserves addition
   as pointwise multiplication, and sends every labelled generator to its coordinate.
7. Conjugating lambda_sigma(a tensor b) = sigma(a)b gives
   gamma(lambda_sigma(a tensor gamma^-1(b))) = (gamma.comp sigma)(a)b.
   Equality on pure tensors gives equality of regular coordinate functions,
   so IsConjugate gives equivariance on all characters. For L=k there is one
   embedding, the norm coordinate is x, and the basis character is the identity. -/
theorem exists_inducedUnitTorus_characters
    (k ks L : Type u) [Field k] [Field ks] [Field L]
    [Algebra k ks] [IsSepClosure k ks] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    ∃ Q : Grp (Over (Spec (.of k))),
      IsAffine Q.X.left ∧ LocallyOfFiniteType Q.X.hom ∧ QuasiCompact Q.X.hom ∧
      IsTorus Q ∧
      ∃ e : ∀ (R : Type u) [CommRing R] [Algebra k R],
        (StandardGroupSchemes.affine k R ⟶ Q.X) ≃* (L ⊗[k] R)ˣ,
      (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
        (f : R →ₐ[k] S) (p : StandardGroupSchemes.affine k R ⟶ Q.X),
        e S (StandardGroupSchemes.map k f ≫ p) =
          Units.map (Algebra.TensorProduct.map (AlgHom.id k L) f).toMonoidHom (e R p)) ∧
      ∃ theta : (L ⊗[k] ks) ≃ₐ[k] ((L →ₐ[k] ks) → ks),
      (∀ (a : L) (b : ks) (σ : L →ₐ[k] ks), theta (a ⊗ₜ[k] b) σ = σ a * b) ∧
      ∃ chi : FreeAbelianGroup (L →ₐ[k] ks) ≃ GeometricCharacters ks Q,
      (∀ x y : FreeAbelianGroup (L →ₐ[k] ks),
        (chi (x + y)).hom.hom = (chi x).hom.hom * (chi y).hom.hom) ∧
      (∀ (γ : ks ≃ₐ[k] ks) (x : FreeAbelianGroup (L →ₐ[k] ks)),
        IsConjugate γ (chi x)
          (chi (FreeAbelianGroup.map (fun σ : L →ₐ[k] ks ↦ γ.toAlgHom.comp σ) x))) ∧
      (∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra ks R]
        [IsScalarTower k ks R] (σ : L →ₐ[k] ks)
        (p : StandardGroupSchemes.affine k R ⟶ Q.X)
        (q : StandardGroupSchemes.affine ks R ⟶ ((baseChange (K := ks)).obj Q).X),
        q.left ≫ scalarProjection Q = p.left →
        (Scheme.ΓSpecIso (.of R)).hom
          (q.left.appTop (characterElement (chi (FreeAbelianGroup.of σ)))) =
        Algebra.TensorProduct.productMap
          (((Algebra.ofId ks R).restrictScalars k).comp σ) (AlgHom.id k R)
          (e R p : L ⊗[k] R)) := by
  sorry

end AlgebraicGeometry.MultiplicativeType
