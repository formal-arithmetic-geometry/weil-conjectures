module

public import Sheaf.AlgebraicGeometry.RelativeMorphismsPresheaf
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.AlgebraicGeometry.Gluing

/-! # Affine relative Hom from a finite free source

Source: Stacks Project, more-morphisms.tex, Tag 05Y6,
lemma-hom-from-finite-free-into-affine and equation-hom-functor
(blueprint: lem-sfb-affine-finite-free-hom).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The relative Hom functor from a finite free affine source to an arbitrary affine target
is represented by an affine scheme. The displayed map sends an `S`-map to its composite
with `p` and the pullback of the universal relative morphism. Thus bijectivity is a natural
bijection on all `S`-schemes, compatible with the map to `Mor_S(U,T)`.

Source: Stacks Project, more-morphisms.tex, Tag 05Y6,
lemma-hom-from-finite-free-into-affine and equation-hom-functor
(blueprint: lem-sfb-affine-finite-free-hom).

Proof plan:
1. Present `C` as `R[x_i]/K` using all its elements as generators and all kernel elements
as relations (def-weil-pbc-mv-polynomial-ring, def-weil-pbc-algebra-hom-quotient).
2. For the given basis `e_j` form `P = R[a_ij]` and expand each relation after substituting
`x_i = sum_j a_ij tensor e_j`. Let `J` be the ideal of all coefficients and `D = P/J`.
Uniqueness of these coefficients uses lem-weil-pbc-free-module-base-change-free and
lem-weil-pbc-algebra-tensor-pushout-universal-property.
3. A map `P → A` kills `J` exactly when the corresponding map from `R[x_i]` into
`A tensor B` kills `K`, by linear independence of the base-changed basis.
4. Hence maps `D → A` correspond bijectively to maps `C → A tensor B`, naturally in
all `R`-algebras `A`, without any finite-presentation hypothesis on `C`.
5. The identity of `D` gives the universal relative morphism on `M = Spec D` via
lem-weil-pbc-fibre-product-affine-spectra and def-weil-affine-spectrum.
6. Extend the affine-test bijections to arbitrary test schemes by affine open gluing
(lem-weil-pbc-scheme-morphism-gluing). Check overlaps on affine opens covering them;
no affine-intersection assumption is needed. Pullback of the universal morphism is natural.
7. For an `S`-map into `M`, its composite with `p` is the unique map `a` to `T`.
Apply the preceding bijection for each `a`. For `m = 0`, `B` is zero, `P = R`, `J = 0`,
`M = T`, and the source of each relative morphism is empty, so the same argument applies.
-/
theorem exists_affine_finite_free_hom
    (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (S : Scheme.{u})
    (t : Spec (.of R) ⟶ S) (m : ℕ) (_basis : Module.Basis (Fin m) R B) :
    ∃ (M : Scheme.{u}) (p : M ⟶ Spec (.of R)), IsAffine M ∧
      ∃ b : (relativeMorphismsPresheaf
          (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R C)))).obj (op (Over.mk p)),
        ∀ U : Over S, Function.Bijective
          (fun f : U ⟶ Over.mk (p ≫ t) ↦
            (⟨Over.homMk (f.left ≫ p)
                (by exact (Category.assoc f.left p t).trans f.w),
              (relativeMorphismsPresheaf
                (Spec.map (CommRingCat.ofHom (algebraMap R B)))
                (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map
                  (Over.homMk f.left (by rfl) :
                    Over.mk (f.left ≫ p) ⟶ Over.mk p).op b⟩ :
              Σ a : U ⟶ Over.mk t,
                (relativeMorphismsPresheaf
                  (Spec.map (CommRingCat.ofHom (algebraMap R B)))
                  (Spec.map (CommRingCat.ofHom (algebraMap R C)))).obj
                    (op (Over.mk a.left)))) := by
  sorry

end AlgebraicGeometry
