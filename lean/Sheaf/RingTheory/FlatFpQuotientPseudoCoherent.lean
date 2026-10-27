module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Pseudo-coherence under a quotient of flat finitely presented algebras

Source: Stacks Project, More on Algebra, Tag 0E1T,
lemma-more-relative-pseudo-coherent-is-moot, equivalence (1) with (4)
(blueprint: lem-sfb-flat-fp-quotient-pseudocoherent).
-/

@[expose] public section

set_option autoImplicit false

universe uR uB uA v wA wB

open CategoryTheory

namespace DerivedCategory

/-- Restriction along a surjection between flat finitely presented algebras preserves
and reflects pseudo-coherence, without any Noetherian hypothesis.

Source: Stacks Project, More on Algebra, Tag 0E1T,
lemma-more-relative-pseudo-coherent-is-moot, equivalence (1) with (4)
(blueprint: lem-sfb-flat-fp-quotient-pseudocoherent).

Proof: Choose a finite polynomial presentation π : P = R[x₁,...,xₙ] → B, using
finite presentation and def-weil-pbc-mv-polynomial-ring. Its composite with q is
surjective: lift first through q and then through π. Restricting a representative
complex along qπ is the same as successively restricting along q and π: both
have the same additive groups, differentials and action p • m = q(π(p)) • m.
These exact forgetful functors preserve cohomology, so this identification
passes to the derived categories.

By lem-sfb-flat-fp-polynomial-pseudocoherent, applied to the two flat finitely
presented R-algebras and these presentations, both B[0] and A[0] are
pseudo-coherent over P. Apply lem-sfb-pseudocoherent-algebra-scalar-restriction
(Stacks 064Z) first to P → A and M and then to P → B and q_*M. The former
identifies pseudo-coherence over A with that of (qπ)_*M over P; the latter
identifies pseudo-coherence of q_*M over B with that of π_*(q_*M) over P.
The identified restricted complexes give the desired equivalence. -/
theorem isPseudoCoherent_restrictScalars_iff_of_flat_finitePresentation_quotient
    {R : Type uR} {B : Type uB} {A : Type uA}
    [CommRing R] [CommRing B] [CommRing A]
    (f : R →+* B) (q : B →+* A) (hq : Function.Surjective q)
    (hf_flat : f.Flat) (hqf_flat : (q.comp f).Flat)
    (hf_fp : f.FinitePresentation) (hqf_fp : (q.comp f).FinitePresentation)
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uB uA v} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{max uR uB uA v} B)]
    (M : DerivedCategory (ModuleCat.{max uR uB uA v} A)) :
    IsPseudoCoherent M ↔
      IsPseudoCoherent ((ModuleCat.restrictScalars q).mapDerivedCategory.obj M) := by
  sorry

end DerivedCategory
