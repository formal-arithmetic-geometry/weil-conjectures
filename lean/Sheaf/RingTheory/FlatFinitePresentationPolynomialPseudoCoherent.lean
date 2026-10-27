module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.FlatFinitePresentationModel
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Equalizer
import Sheaf.RingTheory.PolynomialPresentationPseudoCoherence

/-!
# Flat finitely presented algebras over a polynomial presentation

Source: Stacks Project, More on Algebra, Tag 067J,
lemma-flat-finite-presentation-perfect, and Tag 065H, lemma-relatively-pseudo-coherent
(blueprint: lem-sfb-flat-fp-polynomial-pseudocoherent).
-/

@[expose] public section

set_option autoImplicit false

universe uR uC v w

open CategoryTheory

namespace DerivedCategory

/-- A flat finitely presented algebra, placed in degree zero and regarded as a module
via any finite polynomial presentation, is pseudo-coherent. Here `ULift` puts the regular
module in a universe large enough to contain the polynomial ring without identifying the
universes of the two rings. Its module structure is the usual one transported by `ULift.down`.
The conclusion means exactly the existence of a bounded-above finite free representative.

Source: Stacks Project, More on Algebra, Tag 067J,
lemma-flat-finite-presentation-perfect, pseudo-coherence consequence; Tag 065H,
lemma-relatively-pseudo-coherent, independence of presentation
(blueprint: lem-sfb-flat-fp-polynomial-pseudocoherent).

Proof:
1. Use lem-weil-pbc-flat-finite-presentation-model to descend R → C to a flat finitely
   presented R₀ → C₀ with R₀ finitely presented over the integers. The integers are
   Noetherian by division with remainder. Dropping the finite relations gives finite type,
   and lem-weil-pbc-finite-type-algebra-noetherian makes R₀ and each finite polynomial
   algebra over R₀ Noetherian. This imposes no Noetherian hypothesis on R or C.
2. Choose a finite polynomial presentation P₀ → C₀. The P₀-module C₀ is cyclic, generated
   by 1. Apply lem-weil-pbc-finite-free-resolution-noetherian to obtain an augmented exact
   resolution by finite free P₀-modules Fᵢ.
3. Each Fᵢ is free, hence flat over R₀, using its monomial and standard-vector basis.
   Set K₋₁ = C₀ and take successive kernels Kᵢ of Fᵢ → Kᵢ₋₁. Starting with flat C₀,
   lem-weil-pbc-flat-ses-kernel-flat inductively makes all Kᵢ flat over R₀.
4. Apply lem-weil-pbc-flat-quotient-tensor-injective to these short exact sequences with
   tensor factor R. Their quotients are flat, so tensoring preserves exactness. Identify
   R ⊗ P₀ with P₁ = R[z₁,...,zₜ] by the monomial formula, and R ⊗ Fᵢ with finite free
   P₁-modules. The model comparison identifies R ⊗ C₀ with C. Thus this resolves C over
   the induced surjection P₁ → C, even when R is not flat over R₀.
5. Put these free terms in degrees -i and zero in positive degrees. The augmentation to
   C[0] is a quasi-isomorphism by exactness. The definition def-pc-ring-pseudo-coherent-complex
   gives pseudo-coherence over P₁. Apply
   lem-sfb-polynomial-presentation-pseudocoherence-invariance to the induced presentation
   and the supplied π, obtaining the conclusion over its polynomial ring.
Zero variables, zero rings, zero ranks and an unbounded negative tail are allowed. -/
theorem isPseudoCoherent_single_polynomialPresentation_of_flat_finitePresentation
    {R : Type uR} {C : Type uC} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C] (hflat : (algebraMap R C).Flat)
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] C) (hπ : Function.Surjective π)
    [HasDerivedCategory.{w} (ModuleCat.{max uR uC v} (MvPolynomial (Fin n) R))] :
    IsPseudoCoherent
      ((singleFunctor (ModuleCat.{max uR uC v} (MvPolynomial (Fin n) R)) 0).obj
        ((ModuleCat.restrictScalars π.toRingHom).obj
          (ModuleCat.of C (ULift.{max uR v} C)))) := by
  sorry

end DerivedCategory
