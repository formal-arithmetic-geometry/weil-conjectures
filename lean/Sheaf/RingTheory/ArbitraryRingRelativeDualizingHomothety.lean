/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.Algebra.Homology.ModuleHomComplex
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.AlgebraicGeometry.AffineRelativeTorAmplitudeCriterion

/-! # Relative dualizing homothety over arbitrary commutative rings

Source: Stacks Project, Dualizing Complexes, Tags 0E2C and 0E2G,
`definition-relative-dualizing-complex` and `lemma-relative-dualizing-RHom`
(blueprint: lem-sfb-arbitrary-ring-relative-dualizing-homothety).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A relative dualizing complex has scalar derived endomorphisms. The homothety is
`MonoidalClosed.curry' (𝟙 M)`: the transpose of the right unit action, with source
A[0], the derived tensor unit. The two equivalences are fixed on every scalar, so
identify the scalar ring and its units with endomorphisms and automorphisms.
No Noetherian or nonzero-ring assumption is imposed.

Source: Stacks Project, Tags 0E2C and 0E2G, lemma-relative-dualizing-RHom
(blueprint: lem-sfb-arbitrary-ring-relative-dualizing-homothety).

Proof:
1. Apply lem-trf-flat-subring-model-system to obtain a flat finitely presented model
R₀ → A₀ over a finite type integer subalgebra and its directed tail Rᵢ, Aᵢ.
Integers are a PID by division with remainder. The PID Noetherian theorem and
finite-type Noetherian theorem make the Rᵢ and Aᵢ Noetherian. No injectivity of
Aᵢ → A is used.
2. Choose a polynomial presentation P₀ onto A₀ and C₀ = RHom_P₀(A₀,P₀)[n].
lem-trf-algebraic-diagonal-class-normalization makes C₀ relatively perfect and
its diagonal Hom A₀. Choose the degree-zero class over 1 using
lem-pur-rhom-global-sections. The algebraic diagonal-generator base-change theorem
preserves this condition and generator in Cᵢ and C, without flat base change.
3. Translate C₀ by the affine quasi-coherent derived equivalence. The affine
pseudo-coherent and relative Tor criteria give relative perfection on Spec A₀.
The flat locally finitely presented relative-perfect base-change theorem applies.
Affine fibre products and affine derived pullback/tensor identify its outputs
with the tilde complexes of Cᵢ and C. The same affine criteria give their relative
perfection; quasi-compactness here supplies a global interval.
4. Over each Noetherian pair the diagonal generator makes its multiplication
transpose an isomorphism on every cohomology. The algebraic diagonal-class
normalization theorem applied to Cᵢ twice makes its actual scalar homothety invertible.
5. Apply lem-sfb-relative-perfect-hom-filtered-colimit to C₀ and C₀[q]. The Hom
shift formula and RHom/global-sections identify the colimit groups with A when
q = 0 and zero otherwise. Tensor extension preserves scalar identities, so the
map in degree zero is the actual scalar map. Consequently the homothety of C
is a quasi-isomorphism, hence invertible in the localization. No arbitrary
unbounded Hom base-change assertion is needed.
6. lem-sfb-arbitrary-ring-relative-dualizing-isomorphism gives M ≅ C. Conjugation
of derived Hom transports homothety since this isomorphism is A-linear; thus
the homothety of M is invertible. No chosen-class normalization is required.
7. RHom/global-sections and the Hom shift formula identify Hom(M,M[q]) with
H^q(A[0]). Negative groups vanish. In degree zero scalar multiplication is
bijective and preserves addition, multiplication and one, giving the ring
equivalence. Taking its units gives the automorphism equivalence. For A = 0,
all objects and groups concerned are zero and the automorphism group is trivial. -/
theorem arbitraryRing_relativeDualizing_homothety
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (_hflat : (algebraMap R A).Flat) [Algebra.FinitePresentation R A]
    (M : DerivedCategory (ModuleCat.{u} A))
    (_hpc : DerivedCategory.IsPseudoCoherent M)
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
      i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj M) ⊗
            (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Q)))
    (_hdiag : Nonempty
      ((ordinaryModuleDerivedInternalHom (A ⊗[R] A)).obj
          (op (relativeDualizingModuleDiagonal R A),
            (relativeDualizingDerivedExtension
              (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom).obj M) ≅
        relativeDualizingModuleDiagonal R A)) :
    IsIso (MonoidalClosed.curry' (𝟙 M)) ∧
      (∃ e : A ≃+* End M, ∀ a : A, e a = a • 𝟙 M) ∧
      (∃ e : Aˣ ≃* Aut M, ∀ a : Aˣ, (e a).hom = (a : A) • 𝟙 M) ∧
      ∀ i : ℤ, i < 0 → Subsingleton (M ⟶ M⟦i⟧) := by
  sorry

end AlgebraicGeometry
