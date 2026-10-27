module

public import Sheaf.RingTheory.FlatAlgebraDeformationTangentModule
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Sheaf.RingTheory.AdicCompletionFlatDeformationFunctor
import Sheaf.RingTheory.CompletionReflectsFlatLiftability
import WeilConjectures.Algebra.FiniteTypeLiftNilpotent

/-! # Deformations of an affine isolated singularity and its completed local rings

Source: Stacks Project, examples-defos.tex, Tags 0DZF (lemma-isolated),
0DYV (lemma-completion), and 0DZ5 (lemma-smooth-completion)
(blueprint: lem-sfb-isolated-affine-completion-deformation).

The completion at a marked point uses the localization at the inverse image of the
complement of its maximal ideal. Thus it is the actual completed local ring, with
no choice of a prime ideal of the deformation. The finite-quotient formulas specify
all canonical maps. Tangent operations are the square-zero deformation operations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ArtinDeformation

namespace Algebra.FlatDeformation

variable {k : Type u} [Field k]

/-- The ideal-adic completion after localization at the specified multiplicative set.
Source: Stacks, Tag 0DZF (blueprint: lem-sfb-isolated-affine-completion-deformation). -/
abbrev LocalizedCompletion {R : Type u} [CommRing R] (S : Submonoid R) (I : Ideal R) :=
  AdicCompletion (I.map (algebraMap R (Localization S))) (Localization S)

/-- The canonical map on localized completions, characterized on every finite quotient.
Representatives are taken in the localized ring, so this condition also fixes every
fraction, and includes the level zero quotient.
Source: Stacks, Tags 0DYV and 0DZF
(blueprint: lem-sfb-isolated-affine-completion-deformation). -/
def IsLocalizedCompletionMap {R R' : Type u} [CommRing R] [CommRing R']
    (S : Submonoid R) (S' : Submonoid R') (I : Ideal R) (I' : Ideal R')
    (f : R →+* R') (g : LocalizedCompletion S I →+* LocalizedCompletion S' I') : Prop :=
  ∀ (n : ℕ) (x : LocalizedCompletion S I) (a : R) (s : S),
    AdicCompletion.evalₐ (I.map (algebraMap R (Localization S))) n x =
      Ideal.Quotient.mk ((I.map (algebraMap R (Localization S))) ^ n)
        (IsLocalization.mk' (Localization S) a s) →
    ∀ t : S', (t : R') = f s →
      AdicCompletion.evalₐ (I'.map (algebraMap R' (Localization S'))) n (g x) =
        Ideal.Quotient.mk ((I'.map (algebraMap R' (Localization S'))) ^ n)
          (IsLocalization.mk' (Localization S') (f a) t)

variable {P : Type u} [CommRing P] [Algebra k P]

/-- The multiplicative set defining the local ring at the marked special-fibre point.
Source: Stacks, Tag 0DZF (blueprint: lem-sfb-isolated-affine-completion-deformation). -/
def pointDenominators (m : Ideal P) [m.IsPrime] {A : TestCategory k k}
    (Q : Groupoid P A) : Submonoid (algebra Q) :=
  m.primeCompl.comap (marking Q).toRingHom

/-- The completed local ring of a marked deformation at the inverse-image maximal ideal.
Source: Stacks, Tags 0DYV and 0DZF
(blueprint: lem-sfb-isolated-affine-completion-deformation). -/
abbrev pointCompletion (m : Ideal P) [m.IsPrime] {A : TestCategory k k}
    (Q : Groupoid P A) :=
  LocalizedCompletion (pointDenominators m Q) (ideal m Q)

/-- Complete Noetherian local deformations, with completeness for the maximal ideal.
Source: Stacks, Tag 0DYV, and Tag 0DYC (lemma-flat-completion)
(blueprint: lem-sfb-isolated-affine-completion-deformation). -/
def IsCompleteLocalDeformation {B : Type u} [CommRing B] [Algebra k B]
    {A : TestCategory k k} (D : Groupoid B A) : Prop :=
  ∃ h : IsLocalRing (algebra D), IsNoetherianRing (algebra D) ∧
    IsAdicComplete (@IsLocalRing.maximalIdeal (algebra D) _ h) (algebra D)

variable {r : ℕ} (m : Fin r → Ideal P) [∀ i, (m i).IsMaximal]

/-- The special-fibre completed local ring P_m completed at its maximal ideal.
Source: Stacks, Tag 0DZF (blueprint: lem-sfb-isolated-affine-completion-deformation). -/
abbrev completedFibre (i : Fin r) := LocalizedCompletion (m i).primeCompl (m i)

/-- Exact realization of the completed-local-ring functors, including markings,
continuous arrows, and compatibility with all Artinian base changes.
The source groupoids already have finite-type algebras and the target groupoids
already have complete Noetherian local algebras; hence no extra objects are included.
Source: Stacks, Tags 0DZF and 0DYV
(blueprint: lem-sfb-isolated-affine-completion-deformation). -/
def IsPointCompletionFunctor
    (F : ∀ (A : TestCategory k k) (i : Fin r), Groupoid P A ⥤ Groupoid (completedFibre m i) A)
    (e : ∀ (A : TestCategory k k) (i : Fin r) (Q : Groupoid P A),
      algebra ((F A i).obj Q) ≃ₐ[k] pointCompletion (m i) Q) : Prop :=
  (∀ (A : TestCategory k k) (Q : Groupoid P A), (scalar Q).toRingHom.FiniteType) ∧
  (∀ (A : TestCategory k k) (i : Fin r) (D : Groupoid (completedFibre m i) A),
    IsCompleteLocalDeformation D) ∧
  (∀ (A : TestCategory k k) (i : Fin r) (Q : Groupoid P A) (a : ring A),
    e A i Q (scalar ((F A i).obj Q) a) =
      algebraMap (Localization (pointDenominators (m i) Q)) (pointCompletion (m i) Q)
        (algebraMap (algebra Q) (Localization (pointDenominators (m i) Q)) (scalar Q a))) ∧
  (∀ (A : TestCategory k k) (i : Fin r) (Q : Groupoid P A),
    IsLocalizedCompletionMap (pointDenominators (m i) Q) (m i).primeCompl
      (ideal (m i) Q) (m i) (marking Q).toRingHom
      ((marking ((F A i).obj Q)).toRingHom.comp (e A i Q).symm.toRingHom)) ∧
  (∀ (A : TestCategory k k) (i : Fin r) (Q Q' : Groupoid P A) (f : Q ⟶ Q'),
    IsLocalizedCompletionMap (pointDenominators (m i) Q) (pointDenominators (m i) Q')
      (ideal (m i) Q) (ideal (m i) Q') (hom f).toRingHom
      ((e A i Q').toRingHom.comp
        ((hom ((F A i).map f)).toRingHom.comp (e A i Q).symm.toRingHom))) ∧
  (∀ (A : TestCategory k k) (i : Fin r) (D D' : Groupoid (completedFibre m i) A)
      (f : D ⟶ D') (h : IsLocalRing (algebra D)) (h' : IsLocalRing (algebra D')) (n : ℕ),
    (@IsLocalRing.maximalIdeal (algebra D) _ h) ^ n ≤
      Ideal.comap (hom f).toRingHom ((@IsLocalRing.maximalIdeal (algebra D') _ h') ^ n)) ∧
  (∀ (A A' : TestCategory k k) (f : A ⟶ A') (Q : Groupoid P A) (Q' : Groupoid P A')
      (q : algebra Q →ₐ[k] algebra Q'), IsBaseChange f Q Q' q →
    ∀ i : Fin r, ∃! j : algebra ((F A i).obj Q) →ₐ[k] algebra ((F A' i).obj Q'),
      IsBaseChange f ((F A i).obj Q) ((F A' i).obj Q') j ∧
      IsLocalizedCompletionMap (pointDenominators (m i) Q) (pointDenominators (m i) Q')
        (ideal (m i) Q) (ideal (m i) Q') q.toRingHom
        ((e A' i Q').toRingHom.comp (j.toRingHom.comp (e A i Q).symm.toRingHom)))

/-- Smoothness with all the specified reduction isomorphisms: j_i records D_i tensor R
identified with F_i(Q), and the equation on completions says that beta_i reduces to j_i.
Source: Stacks, Tags 0DZF and 0DZ5, and formal-defos.tex Tag 0DYP
(blueprint: lem-sfb-isolated-affine-completion-deformation). -/
def IsPointCompletionSmooth
    (F : ∀ (A : TestCategory k k) (i : Fin r), Groupoid P A ⥤ Groupoid (completedFibre m i) A)
    (e : ∀ (A : TestCategory k k) (i : Fin r) (Q : Groupoid P A),
      algebra ((F A i).obj Q) ≃ₐ[k] pointCompletion (m i) Q) : Prop :=
  ∀ (A' A : TestCategory k k) (f : A' ⟶ A), Function.Surjective (map f) →
    ∀ (Q : Groupoid P A) (D : ∀ i : Fin r, Groupoid (completedFibre m i) A')
      (j : ∀ i : Fin r, algebra (D i) →ₐ[k] algebra ((F A i).obj Q)),
      (∀ i : Fin r, IsBaseChange f (D i) ((F A i).obj Q) (j i)) →
      ∃ (Q' : Groupoid P A') (q : algebra Q' →ₐ[k] algebra Q)
        (beta : ∀ i : Fin r, (F A' i).obj Q' ≅ D i),
        IsBaseChange f Q' Q q ∧
        ∀ i : Fin r,
          IsLocalizedCompletionMap (pointDenominators (m i) Q') (pointDenominators (m i) Q)
            (ideal (m i) Q') (ideal (m i) Q) q.toRingHom
            ((e A i Q).toRingHom.comp
              (((j i).comp (hom (beta i).hom)).toRingHom.comp (e A' i Q').symm.toRingHom))

/-- The induced tangent map is an isomorphism for the canonical deformation operations.
Its underlying map is fixed on every actual dual-number deformation.
Source: Stacks, Tags 0DZF, 0DZ4 and 0DY3
(blueprint: lem-sfb-isolated-affine-completion-deformation). -/
def HasPointCompletionTangentEquiv
    (F : ∀ (A : TestCategory k k) (i : Fin r), Groupoid P A ⥤ Groupoid (completedFibre m i) A) :
    Prop :=
  ∃ (_ : AddCommGroup (Tangent (k := k) P)) (_ : Module k (Tangent (k := k) P))
    (_ : ∀ i : Fin r, AddCommGroup (Tangent (k := k) (completedFibre m i)))
    (_ : ∀ i : Fin r, Module k (Tangent (k := k) (completedFibre m i)))
    (dF : Tangent (k := k) P ≃ₗ[k] (∀ i : Fin r, Tangent (k := k) (completedFibre m i))),
    IsCanonicalTangentModule (k := k) P ∧
    (∀ i : Fin r, IsCanonicalTangentModule (k := k) (completedFibre m i)) ∧
    ∀ Q : Groupoid P (squareZeroTest (R := k) (k := k) k),
      dF (tangentClass (k := k) P Q) =
        fun i ↦ tangentClass (k := k) (completedFibre m i) ((F _ i).obj Q)

/-- The completed-local-ring deformation functor is smooth and tangent-isomorphic.
Source: Stacks Project, examples-defos.tex, Tag 0DZF (lemma-isolated), second paragraph;
Tags 0DYV (lemma-completion) and 0DZ5 (lemma-smooth-completion)
(blueprint: lem-sfb-isolated-affine-completion-deformation).

Proof:
1. Put J equal to the intersection of the maximal ideals, or top for the empty list.
Finite-type-algebra-noetherian and artinian-local-noetherian-nilpotent give Noetherian
rings and nilpotent reduction kernels. The inverse images of m_i are maximal. Apply
lem-sfb-adic-completion-flat-deformation-functor to P,J. All flat marked source
objects are finite type by lem-weil-pbc-finite-type-lift-nilpotent.
2. The m_i and their powers are pairwise comaximal. Intersection equals product,
so J^n is their power intersection. Lem-pc-crt-ideal-quotient-product identifies each
quotient with the product. P/m_i^n is already local, by a finite geometric series
inverting the nilpotent error. Compatible sequences identify the J-completion with
the product of the completed local rings, also for every marked deformation.
3. Lem-weil-pbc-lift-idempotents-locally-nilpotent lifts the coordinate idempotents
uniquely. They remain orthogonal and sum to one, and split every product deformation
into its factors. The factors are flat direct summands. Completion-flat-deformation-
functor makes them complete Noetherian local rings. Isomorphisms preserve maximal
ideal powers, hence are continuous. The splitting respects all marked base changes.
4. Lem-sfb-exal-completion-smooth-complement with B=N=P gives the Exal isomorphism.
Lem-sfb-ring-deformation-smoothness-test identifies Exal with the dual-number tangent
space and its Baer operations. Completing the extension is exactly the above functor;
the product splitting therefore identifies its actual tangent map, coordinatewise.
5. Lem-sfb-completion-reflects-flat-liftability gives existence of a source lift for
every small extension whenever the completed object lifts. Tangent surjectivity and
lem-sfb-ring-deformation-smoothness-test give smoothness with prescribed markings for
every surjection. Take the product of the D_i and their specified reduction maps,
apply the criterion, and project its marked isomorphism to every factor. Nilpotent
finite-type lifting makes the lifted source finite type.
6. For r=0, J=top, its completion is zero and the product groupoid is terminal.
A deformation D of zero satisfies D=m_A D and hence D=0 by nilpotence. The same
argument applies: P is everywhere smooth and its tangent space is zero. If P=0,
all deformation groupoids are terminal. Listed points need not actually be singular,
and their residue fields need not equal k.
-/
theorem isolatedAffine_completion_deformation
    [Algebra.FiniteType k P] (hdistinct : Function.Injective m)
    (hsmooth : ∀ p : Spec (CommRingCat.of P),
      (∀ i : Fin r, p.asIdeal ≠ m i) →
        ∃ U : (Spec (CommRingCat.of P)).Opens, p ∈ U ∧
          AlgebraicGeometry.Smooth (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k P)))) :
    ∃ (F : ∀ (A : TestCategory k k) (i : Fin r),
        Groupoid P A ⥤ Groupoid (completedFibre m i) A)
      (e : ∀ (A : TestCategory k k) (i : Fin r) (Q : Groupoid P A),
        algebra ((F A i).obj Q) ≃ₐ[k] pointCompletion (m i) Q),
      IsPointCompletionFunctor m F e ∧ IsPointCompletionSmooth m F e ∧
        HasPointCompletionTangentEquiv m F := by
  sorry

end Algebra.FlatDeformation
