/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Strict henselization from etale triples

Source: Stacks Project, Algebra, Lemmas Tags 04GW and 04GP
(blueprint: lem-weil-pbc-strict-henselization-triples).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The category of etale residue triples is filtered and its ring colimit is strictly
henselian with the prescribed separable closure as residue field.
Source: Stacks Project, Algebra, Lemmas Tags 04GW and 04GP
(blueprint: lem-weil-pbc-strict-henselization-triples).

Proof:
1. Triples are etale R-algebras pointed in K, since a map to a field factors uniquely
through the residue field of its kernel.
2. Finite presentation gives essential smallness; construct the ring colimit using a
small skeleton (lem-weil-pbc-affine-etale-essentially-small-cover and
lem-weil-pbc-colimit-initial-full-subcategory).
3. Tensor products give common successors, including the identity triple for nonemptiness
(lem-weil-pbc-etale-ring-base-change, lem-weil-pbc-etale-composition-cancellation).
4. For parallel maps beta1, beta2 : S → S', form E = S' ⊗[S] S' using these maps,
then S'' = E ⊗[S' ⊗[R] S'] S' using multiplication on the last factor. Both
base changes are etale by the same base-change and composition lemmas. The two maps
to K agree, hence extend to S''; its kernel and residue embedding define a triple.
The rightmost S' → S'' commutes with the maps to K and equalizes beta1 and beta2,
since beta1(s) ⊗ 1 = 1 ⊗ beta2(s) in E. This gives filteredness.
5. The compatible maps to K induce psi. Inverting an element with nonzero image shows
that the colimit is local, with maximal ideal ker psi.
6. The etale prime-generation lemma lem-weil-pbc-etale-prime-generates-maximal, followed
by localization away from the pointed prime, shows ker psi = p C: represent an
element of the kernel by f ∈ q at a stage S. Its image in S_q lies in p S_q; clearing
denominators gives u ∉ q with u f ∈ p S. The triple S_u makes f lie in p S_u.
The reverse inclusion follows because the structural map to K kills p.
7. Descend the finitely many coefficients of a monic polynomial to one stage, and use
the standard etale algebra localized at its derivative to lift each simple root in K
(lem-weil-pbc-filtered-colimit-algebras-elementwise and
lem-weil-pbc-standard-etale-monic-derivative).
8. The image of psi is a field containing kappa(p). Separability of every element of K
and step 7 imply surjectivity: lift the coefficients of its monic separable minimal
polynomial to C, then lift its simple root using step 7. The induced quotient
isomorphism identifies the residue
field with K, and contraction of the maximal ideal is p.
9. Step 7 and lem-weil-pbc-henselian-local-root-lifting give henselianity. The residue
field is K, hence separably closed, giving strict henselianity.
-/
theorem strictHenselization_triples
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K] :
    IsFiltered (EtaleResidueTriples R p K
        (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))) ∧
      ∃ c : Cocone (etaleResidueTriplesRingDiagram R p K
          (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))),
        Nonempty (IsColimit c) ∧
        ∃ (_ : IsLocalRing c.pt) (ρ : R ⟶ c.pt) (ψ : c.pt →+* K),
          (∀ t, t.α ≫ c.ι.app t = ρ) ∧
          (∀ t, ψ.comp (c.ι.app t).hom =
            ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) ∧
          Function.Surjective ψ ∧
          IsLocalRing.maximalIdeal c.pt = RingHom.ker ψ ∧
          RingHom.ker ψ = p.asIdeal.map ρ.hom ∧
          (RingHom.ker ψ).comap ρ.hom = p.asIdeal ∧
          (∃ e : (c.pt ⧸ IsLocalRing.maximalIdeal c.pt) ≃+* K,
            e.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal c.pt)) = ψ) ∧
          IsStrictlyHenselianLocalRing c.pt := by
  sorry

end AlgebraicGeometry.Scheme
