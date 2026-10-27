/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.Stability
import Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentExchange
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.TraceFormula.AlgebraicShriekCalculus
import Sheaf.TraceFormula.AlgebraicShriekRelativePerfect
import Mathlib.RingTheory.FiniteType
import Sheaf.TraceFormula.FlatPolynomialQuotientPerfect
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses

/-! # Algebraic diagonal Hom and its generator after arbitrary scalar extension

Source: Stacks Project, dualizing.tex, Tag 0E2F, part (2) and the final generator assertion;
Definition 0E2C supplies the relative-perfection hypotheses.
(blueprint: lem-sfb-algebraic-diagonal-generator-base-change).

We use the canonically commuted presentation `T tensor_R A` of `A tensor_R T`.
The generator conclusion is written on the actual scalar-extended arrow, before the
canonical diagonal and first-pullback identifications. Multiplication by `a'` is
precomposition by the scalar `a' tensor 1` on the extended source. Under those
B'-linear identifications this is exactly multiplication by `a'` on A'[0]. Thus
surjectivity here says that the specified image gamma', rather than an unspecified
class or chosen comparison, generates the primed diagonal Hom module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The actual coefficient map B to B', sending a tensor b to a' tensor b'.
Here A' is T tensor_R A, so a' is 1 tensor a. This is Mathlib's heterobasic
algebra tensor map, with its two coefficient compatibilities supplied by the
algebra-homomorphism and scalar-tower identities.
Source: Stacks Project, Tag 0E2F, the scalar-extension map of diagonal algebras
(blueprint: lem-sfb-algebraic-diagonal-generator-base-change). -/
def algebraicDiagonalBaseChangeRingMap (R A T : Type u)
    [CommRing R] [CommRing A] [CommRing T] [Algebra R A] [Algebra R T] :
    (A ⊗[R] A) →+* ((T ⊗[R] A) ⊗[T] (T ⊗[R] A)) :=
  Algebra.TensorProduct.mapRingHom (algebraMap R T)
    (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
    (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
    ((Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).comp_algebraMap.trans
      (IsScalarTower.algebraMap_eq R T (T ⊗[R] A)))
    ((Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).comp_algebraMap.trans
      (IsScalarTower.algebraMap_eq R T (T ⊗[R] A)))

/-- Arbitrary scalar extension preserves the diagonal Hom and the image of its generator.
Surjectivity of a ↦ multiplication by a followed by gamma is the generator condition,
with the action explicitly by precomposition. The same formula on the actual extended
arrow expresses the primed condition before the canonical B'-linear identifications.
No flatness of R to T and no Noetherian or nonzero-ring assumption is used.
Source: Stacks Project, Tag 0E2F(2) and its final assertion, Definition 0E2C
(blueprint: lem-sfb-algebraic-diagonal-generator-base-change).

Proof (the eight steps of the DAG):
1. Flat module base change and the tensor comparison of
lem-sfb-perfect-coinduction-tor-independent-exchange identify the extended diagonal
with A'[0], and the extended first pullback with the first pullback of M'. These
identifications are natural in morphisms and respect further scalar extension.
2. Bounded-above finite-free representatives preserve pseudo-coherence after scalar
extension. The bounded flat model of lem-sfb-relative-rhom-finite-flat-base-change-model,
with flat module base change and lem-weil-pbc-flat-tensor-exact, preserves finite relative
Tor amplitude and supplies the same properties after the first coprojection.
3. Over a Noetherian base choose a finite polynomial presentation P onto A. The model
V = RHom_P(A,P)[e] is relatively perfect by lem-trf-algebraic-shriek-relative-perfect.
The flat base-change, surjection and composition clauses of
lem-trf-algebraic-shriek-calculus identify its diagonal Hom with A[0].
4. By lem-trf-flat-polynomial-quotient-perfect, A is perfect over P. Perfect coinduction
exchange identifies its scalar extension to every Noetherian target, including residue
fields, with that target's polynomial model. The tensor comparison checks Tor
independence without requiring the base extension to be flat.
5. lem-sfb-flat-fp-quotient-pseudocoherent makes the diagonal pseudo-coherent. Apply
lem-sfb-relative-rhom-finite-flat-base-change-model to obtain a bounded-below flat Hom
complex E computing the diagonal Hom and all its scalar extensions, with the specified
normalization on degree-zero classes.
6. The residue-field calculation and lem-sfb-fibrewise-flat-complex-concentration give
the universal truncation zigzag E tensor T to H^0(E) tensor T in degree zero.
lem-pur-rhom-global-sections identifies its class map with scalar extension of actual
diagonal morphisms. Hence generators remain generators, compatibly with iteration.
7. lem-trf-flat-subring-model-system descends A to a flat finitely presented algebra
over a finite-type Z-subalgebra. This base is Noetherian by the elementary Noetherianity
of Z and lem-weil-pbc-finite-type-algebra-noetherian. Extend its polynomial model V to N.
The preceding steps apply to N; lem-sfb-arbitrary-ring-relative-dualizing-isomorphism
gives an isomorphism N to the supplied M, with no chosen-generator normalization.
8. Postcomposition with this isomorphism is A-linear for the precomposition action.
Pull gamma back to N, apply step 6 to the successive extensions, and extend the
isomorphism back to M'. Tensoring the generating surjection remains surjective, since
every pure tensor has a preimage. Naturality gives precisely the extended gamma.
All arguments include the zero algebra A' and the zero Hom module. -/
theorem algebraicDiagonalGenerator_baseChange
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (hflat : RingHom.Flat (algebraMap R A)) [Algebra.FinitePresentation R A]
    (M : DerivedCategory (ModuleCat.{u} A))
    (hM : DerivedCategory.IsPseudoCoherent M)
    (hTor : ∃ a b : ℤ, a ≤ b ∧ ∀ (N : ModuleCat.{u} R) (i : ℤ),
      i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj M) ⊗
            DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj N))))
    (hHom : Nonempty
      ((ordinaryModuleDerivedInternalHom (A ⊗[R] A)).obj
        (op (relativeDualizingModuleDiagonal R A),
          (ModuleCat.ordinaryDerivedExtendScalars
            (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom).obj M) ≅
        relativeDualizingModuleDiagonal R A))
    (γ : relativeDualizingModuleDiagonal R A ⟶
      (ModuleCat.ordinaryDerivedExtendScalars
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom).obj M)
    (hγ : Function.Surjective (fun a : A ↦
      ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A) a •
        𝟙 (relativeDualizingModuleDiagonal R A)) ≫ γ))
    (T : Type u) [CommRing T] [Algebra R T] :
    Nonempty
      ((ordinaryModuleDerivedInternalHom ((T ⊗[R] A) ⊗[T] (T ⊗[R] A))).obj
        (op (relativeDualizingModuleDiagonal T (T ⊗[R] A)),
          (ModuleCat.ordinaryDerivedExtendScalars
            (Algebra.TensorProduct.includeLeft :
              (T ⊗[R] A) →ₐ[T] (T ⊗[R] A) ⊗[T] (T ⊗[R] A)).toRingHom).obj
            ((ModuleCat.ordinaryDerivedExtendScalars
              (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom).obj M)) ≅
        relativeDualizingModuleDiagonal T (T ⊗[R] A)) ∧
    Function.Surjective (fun a' : T ⊗[R] A ↦
      ((Algebra.TensorProduct.includeLeft :
          (T ⊗[R] A) →ₐ[T] (T ⊗[R] A) ⊗[T] (T ⊗[R] A)) a' •
        𝟙 ((ModuleCat.ordinaryDerivedExtendScalars
          (algebraicDiagonalBaseChangeRingMap R A T)).obj
            (relativeDualizingModuleDiagonal R A))) ≫
      (ModuleCat.ordinaryDerivedExtendScalars
        (algebraicDiagonalBaseChangeRingMap R A T)).map γ) := by
  sorry

end AlgebraicGeometry
