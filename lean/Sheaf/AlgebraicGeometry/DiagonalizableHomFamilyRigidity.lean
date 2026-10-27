module

public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Rigidity of families of homomorphisms between diagonalizable groups

Source: Milne, Algebraic Groups (2017), Theorem 12.36, pp.243--244, and Remark 12.43,
p.245 (blueprint: lem-sfb-diagonalizable-hom-family-rigidity).

The pointwise hypothesis tests every commutative F-algebra, including nonreduced algebras.
Products and morphisms are in the category of schemes over Spec F.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A connected affine family of homomorphisms between diagonalizable groups is constant.
Source: Milne, Algebraic Groups (2017), Theorem 12.36, pp.243--244, and Remark 12.43,
p.245 (blueprint: lem-sfb-diagonalizable-hom-family-rigidity).

Proof:
1. Choose the group-scheme identifications and write X = Spec B. The F-point x₀ gives
   b₀ : B → F, so B is nonzero. Use lem-weil-pbc-fibre-product-affine-spectra,
   def-weil-affine-spectrum, and lem-weil-pbc-algebra-tensor-pushout-universal-property
   to identify X × D₁ with Spec(B ⊗ F[M₁]) and then Spec B[M₁]. The tensor/group-algebra
   isomorphism sends b ⊗ e_m to b e_m, with inverse on finite sums. Thus φ gives
   f : F[M₂] → B[M₁]. Write f(e_n) = ∑ a_(n,m) e_m. Test the homomorphism condition on
   A = B[M₁ ⊕ M₁], with the two universal D₁-points, to obtain
   ∑ a_(n,m) e_(m,m) = ∑ a_(n,m) a_(n,l) e_(m,l). Testing the identity on A = B gives
   ∑ a_(n,m) = 1. These tests retain all nilpotents.
2. Coefficient comparison in the finitely supported group algebra gives idempotent
   coefficients a_(n,m)² = a_(n,m), orthogonal for distinct indices, summing to 1.
3. By lem-pc-scheme-connected-iff-idempotents, connectedness of the nonempty X makes
   each coefficient 0 or 1. Since B is nonzero, exactly one is 1: at least one is nonzero
   because the sum is 1, and two coefficients equal to 1 would contradict orthogonality.
   Hence f(e_n) = e_(h(n)) for a unique h(n). No domain hypothesis is used.
4. Pullback along x₀ × id applies b₀ to coefficients and preserves these basis monomials.
   Pullback along the second projection again preserves them. The two resulting algebra
   maps agree on F and every e_n, hence on all finite sums. The uniqueness in
   def-weil-affine-spectrum proves equality of the F-morphisms.
-/
theorem diagonalizable_hom_family_rigidity
    (F : Type u) [Field F] [IsAlgClosed F]
    (D₁ D₂ : Grp (Over (Spec (.of F))))
    [IsAffine D₁.X.left] [IsAffine D₂.X.left]
    [LocallyOfFiniteType D₁.X.hom] [QuasiCompact D₁.X.hom]
    [LocallyOfFiniteType D₂.X.hom] [QuasiCompact D₂.X.hom]
    (M₁ M₂ : Type u) [AddCommGroup M₁] [AddCommGroup M₂]
    [AddGroup.FG M₁] [AddGroup.FG M₂]
    (hD₁ : Nonempty (D₁ ≅ diagonalizableGroup F M₁))
    (hD₂ : Nonempty (D₂ ≅ diagonalizableGroup F M₂))
    (X : Over (Spec (.of F))) [IsAffine X.left] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (x₀ : 𝟙_ (Over (Spec (.of F))) ⟶ X) (φ : X ⊗ D₁.X ⟶ D₂.X)
    (hφ : ∀ (A : Type u) [CommRing A] [Algebra F A]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ X),
      (∃ f : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ D₁.X) →*
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ D₂.X),
        ∀ d, f d = lift x d ≫ φ)) :
    φ = snd X D₁.X ≫ (lift (toUnit D₁.X ≫ x₀) (𝟙 D₁.X) ≫ φ) := by
  sorry

end AlgebraicGeometry
