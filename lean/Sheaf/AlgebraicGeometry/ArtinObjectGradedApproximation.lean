/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.AssociatedGradedRing
import Sheaf.TraceFormula.ArtinApproximationEtaleLocalMap
import Sheaf.AlgebraicGeometry.EtaleCompletionCongruence
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FiniteTypeGRing

/-! # Approximation of an effective object with its jet and associated graded ring

Source: Stacks Project, Artin's Axioms, Tag 07XB, lemma-approximate, affine-base case,
conclusions (1)--(6) (blueprint: lem-sfb-artin-object-graded-approximation).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Approximation of an object of a limit-preserving fibred groupoid by an object
of finite type, preserving a prescribed jet and the graded residue-field algebra.
The common object `z` and its two lifted arrows express the isomorphism between
restrictions over the jet isomorphism. Every arrow in a fibred groupoid is
cartesian. The residue isomorphism `e₀` is tied to `eN` by the quotient square;
the graded ring isomorphism preserves each homogeneous piece and this residue action.

Source: Stacks, Artin's Axioms, Tag 07XB (lemma-approximate), conclusions (1)--(6)
(blueprint: lem-sfb-artin-object-graded-approximation).

Proof: (1) Express C as the directed union of its finitely generated R-subalgebras.
By lem-weil-pbc-spec-small-colimit-limit and object descent, xC descends to z over
one D. By lem-weil-pbc-finite-type-noetherian-finite-presentation, present D by
finitely many variables and relations. (2) Lift generators of the residue field
and of the maximal ideal to obtain a polynomial ring T mapping onto C/m².
Localize at the residue kernel and complete to P. The Noetherianity, localness,
and finite-quotient comparisons in lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-localization-noetherian, lem-weil-pbc-adic-completion-noetherian,
lem-weil-pbc-local-completion-local-ring and lem-weil-pbc-adic-completion-mod-power,
followed by lem-sfb-complete-local-cotangent-graded-rigidity, give P surjecting
onto C. (3) Choose generators b of its kernel and a relation matrix K, using
lem-weil-pbc-noetherian-submodule-finite. Obtain a stability bound h from
lem-sfb-adic-relation-matrix-initial-ideals, and choose M at least N, h and 2.
(4) By lem-weil-pbc-finite-type-over-g-ring and the definition of G-rings the
localized polynomial ring is a G-ring. Apply
lem-trf-artin-approximation-etale-local-map to the equations f(a)=cb and bK=0.
Use lem-weil-pbc-etale-locally-standard to obtain a finite presentation B over T.
(5) Lem-trf-etale-completion-congruence identifies the pointed completion of B
with P. The perturbed b' lie in its maximal ideal; put A=B/(b'). The residue map
is onto k, hence its kernel n is maximal. (6) Congruence gives
(b)+q^M=(b')+q^M; completion modulo powers and localization identify the M-jets
of C and A. Their maps from D agree, so the descended object gives the same
restricted object. Reduce to precision N. (7) The initial-ideal stability lemma
gives equal initial denominators in every degree. Identity on representatives
therefore gives a graded ring isomorphism. Products, units and residue scalars
agree on representatives. Its degree-zero map is the residue map of the common
jet. This is precisely the associated graded ring of
def-weil-pbc-associated-graded-ring. -/
theorem artin_object_graded_approximation
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (hF : IsFibredInGroupoids F)
    (hLimits : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (D : Iᵒᵖ ⥤ Over (Spec (.of R))) (c : Cone D),
      (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
      Nonempty (IsLimit c) → ∀ x : Functor.Fiber F.p c.pt,
        ∃ (i : I) (xi : Functor.Fiber F.p (D.obj (op i))) (a : x.val ⟶ xi.val),
          F.p.IsHomLift (c.π.app (op i)) a)
    (C : Type u) [CommRing C] [Algebra R C] [IsNoetherianRing C] [IsLocalRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap R (C ⧸ IsLocalRing.maximalIdeal C))))]
    [QuasiCompact (Spec.map (CommRingCat.ofHom
      (algebraMap R (C ⧸ IsLocalRing.maximalIdeal C))))]
    (hG : IsGRing (Localization.AtPrime
      (Ideal.comap (algebraMap R C) (IsLocalRing.maximalIdeal C))))
    (xC : Functor.Fiber F.p ((algSpec (.of R)).obj (op (CommAlgCat.of R C))))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.FiniteType R A)
      (n : Ideal A) (_ : n.IsMaximal)
      (y : Functor.Fiber F.p ((algSpec (.of R)).obj (op (CommAlgCat.of R A))))
      (eN : (C ⧸ (IsLocalRing.maximalIdeal C) ^ N) ≃ₐ[R] (A ⧸ n ^ N)),
      (∃ (z : Functor.Fiber F.p ((algSpec (.of R)).obj
          (op (CommAlgCat.of R (C ⧸ (IsLocalRing.maximalIdeal C) ^ N)))))
        (a : z.val ⟶ xC.val) (b : z.val ⟶ y.val),
        F.p.IsHomLift ((algSpec (.of R)).map
          (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R
            ((IsLocalRing.maximalIdeal C) ^ N))).op) a ∧
        F.p.IsHomLift ((algSpec (.of R)).map
          (CommAlgCat.ofHom (eN.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R (n ^ N)))).op) b) ∧
      ∃ (e₀ : (C ⧸ IsLocalRing.maximalIdeal C) ≃ₐ[R] (A ⧸ n)),
        (∀ t : C ⧸ (IsLocalRing.maximalIdeal C) ^ N,
          e₀ (Ideal.Quotient.factorₐ R (Ideal.pow_le_self (Nat.ne_zero_of_lt hN)) t) =
            Ideal.Quotient.factorₐ R (Ideal.pow_le_self (Nat.ne_zero_of_lt hN)) (eN t)) ∧
        ∃ g : (IsLocalRing.maximalIdeal C).associatedGraded ≃+* n.associatedGraded,
          (∀ d : ℕ,
            g '' Set.range (DirectSum.of
              (fun j : ℕ => (IsLocalRing.maximalIdeal C).associatedGradedPiece j) d) =
            Set.range (DirectSum.of (fun j : ℕ => n.associatedGradedPiece j) d)) ∧
          ∀ t : C ⧸ IsLocalRing.maximalIdeal C,
            g (algebraMap (C ⧸ IsLocalRing.maximalIdeal C)
              (IsLocalRing.maximalIdeal C).associatedGraded t) =
            algebraMap (A ⧸ n) n.associatedGraded (e₀ t) := by
  sorry

end AlgebraicGeometry
