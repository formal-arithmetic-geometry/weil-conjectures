module

public import Sheaf.RingTheory.SquareZeroAlgebraClasses
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.FiniteType

import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.KaehlerDifferentialsPolynomialExtension
import WeilConjectures.RingTheory.RingPseudoCoherent
import Sheaf.RingTheory.FinitePolynomialSimplicialResolution
import Sheaf.RingTheory.CotangentResolutionCoherence
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Completion of square-zero extensions away from a smooth open

Source: Stacks Project, Tag 0DZ4, lemma-first-order-completion.
(blueprint: lem-sfb-exal-completion-smooth-complement)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace Algebra.SquareZeroClasses

variable {k B N : Type u} [Field k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N]

/-- The graph of completion, expressed on every finite quotient. The middle algebra
is the completion along the inverse image of `J`; both end markings are the maps
induced on compatible sequences. Quantifying over every quotient and representative
specifies these maps without choosing quotient lifts.

Source: Stacks 0DZ4, first paragraph of proof.
(blueprint: lem-sfb-exal-completion-smooth-complement) -/
def IsCompletion (J : Ideal B) (E : Extension k B N)
    (F : Extension k (AdicCompletion J B) (AdicCompletion J N)) : Prop :=
  ∃ e : AdicCompletion (J.comap E.p.toRingHom) E.extension.Ring ≃ₐ[k] F.extension.Ring,
    (∀ (z : AdicCompletion (J.comap E.p.toRingHom) E.extension.Ring)
      (n : ℕ) (x : E.extension.Ring),
      AdicCompletion.eval (J.comap E.p.toRingHom) E.extension.Ring n z =
        Submodule.Quotient.mk x →
      AdicCompletion.eval J B n (F.p (e z)) = Submodule.Quotient.mk (E.p x)) ∧
    ∀ (z : AdicCompletion J N) (n : ℕ) (x : N),
      AdicCompletion.eval J N n z = Submodule.Quotient.mk x →
      AdicCompletion.eval (J.comap E.p.toRingHom) E.extension.Ring n
        (e.symm (F.i z)) = Submodule.Quotient.mk (E.i x)

/-- A linear equivalence for the natural Baer-sum module structures whose graph on
representatives is precisely completion. The structures are part of the conclusion,
not hypotheses. The graph specifies the actual completed middle algebra and its
kernel and quotient markings, rather than an arbitrary bijection of class sets.

Source: Stacks notation before 0DZ4 and the completion map in its proof.
(blueprint: lem-sfb-exal-completion-smooth-complement) -/
structure CompletionLinearEquiv (J : Ideal B) where
  sourceGroup : AddCommGroup (Classes k B N)
  sourceModule : @Module k (Classes k B N) _ sourceGroup.toAddCommMonoid
  targetGroup : AddCommGroup (Classes k (AdicCompletion J B) (AdicCompletion J N))
  targetModule : @Module k (Classes k (AdicCompletion J B) (AdicCompletion J N)) _
    targetGroup.toAddCommMonoid
  sourceNatural : @IsNaturalModule k B N _ _ _ _ _ sourceGroup sourceModule
  targetNatural : @IsNaturalModule k (AdicCompletion J B) (AdicCompletion J N)
    _ _ _ _ _ targetGroup targetModule
  linearEquiv : @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k) _ _
    (Classes k B N) (Classes k (AdicCompletion J B) (AdicCompletion J N))
    sourceGroup.toAddCommMonoid targetGroup.toAddCommMonoid sourceModule targetModule
  completion : ∀ (E : Extension k B N)
    (F : Extension k (AdicCompletion J B) (AdicCompletion J N)),
    linearEquiv (classOf E) = classOf F ↔ IsCompletion J E F

/-- Completing square-zero extensions is a canonical linear isomorphism when the
finite-type algebra is smooth off the closed locus and the kernel module is finite.

Source: Stacks Project, Tag 0DZ4, lemma-first-order-completion, and its Exal notation.
(blueprint: lem-sfb-exal-completion-smooth-complement)

Proof:
1. The field is Noetherian, hence so is the finite-type algebra. A finite polynomial
simplicial resolution gives a bounded-above finite-free model of the full cotangent
complex: polynomial differentials are finite free. Thus it is pseudo-coherent
(lem-weil-pbc-finite-type-algebra-noetherian, lem-sfb-finite-polynomial-simplicial-resolution,
lem-trf-cotangent-resolution-coherence, lem-weil-pbc-kahler-differentials-polynomial-extension,
def-pc-ring-pseudo-coherent-complex).
2. Positive cotangent Ext is supported on the nonsmooth locus. The supported-complex
completion theorem makes the coefficient map on first Ext an isomorphism, with jointly
injective maps to the finite quotients (lem-sfb-cotangent-ext-smooth-support,
lem-sfb-supported-complex-ext-completion).
3. In an extension the kernel is a finite square-zero ideal. Noetherianity follows from
Noetherianity of its quotient using completion along this nilpotent ideal. Exactness of
completion gives the completed extension. The inverse-image ideal acts on the kernel
through J, so all quotient markings are exactly those in IsCompletion. The completed
base is Noetherian and complete, and its kernel is finite by the tensor description
(lem-weil-pbc-completion-noetherian-quotient-noetherian,
lem-weil-pbc-completion-exact-finite-modules, lem-weil-pbc-adic-completion-noetherian,
lem-weil-pbc-module-completion-complete, lem-weil-pbc-completion-finite-module-tensor).
4. Classification by first cotangent Ext identifies restriction after completion with
the coefficient map. Restriction is injective: a split pullback supplies a map from B
into the completed extension. That extension is Noetherian and complete across its
square-zero ideal, so the map extends by compatible quotient maps to a section over the
completed base (lem-sfb-ring-square-zero-extension-classification,
lem-sfb-finite-square-zero-adic-thickening,
lem-weil-pbc-completion-noetherian-quotient-noetherian).
5. The coefficient isomorphism and restriction injectivity give bijectivity of completion.
The classification respects coefficient pushout and Baer sums. Hence restriction
injectivity also proves additivity and k-linearity, for the natural operations specified
by IsNaturalModule (lem-sfb-ring-square-zero-extension-classification). -/
theorem nonempty_completionLinearEquiv
    (k B N : Type u) [Field k] [CommRing B] [Algebra k B] [FiniteType k B]
    [AddCommGroup N] [Module B N] [Module.Finite B N] (J : Ideal B)
    (hsmooth : ∀ p : Spec (CommRingCat.of B),
      p ∉ PrimeSpectrum.zeroLocus (J : Set B) →
      ∃ U : (Spec (CommRingCat.of B)).Opens, p ∈ U ∧
        AlgebraicGeometry.Smooth (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)))) :
    Nonempty (CompletionLinearEquiv (N := N) (k := k) J) := by
  sorry

end Algebra.SquareZeroClasses
