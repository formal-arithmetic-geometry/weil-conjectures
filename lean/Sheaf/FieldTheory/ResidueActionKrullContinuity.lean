module

public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Krull topology and continuity of residue actions

Source: Stacks Project, Fields, Tag 0BMJ (`lemma-galois-profinite`), and
Fundamental Groups of Schemes, Tag 0BSW (`lemma-identify-inertia`), with the
finite-lift argument spelled out in the DAG node.
(blueprint: lem-dl-a1-residue-action-krull-continuity)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace IntermediateField

/-- The underlying-automorphism identification for an arbitrary intermediate field is
bicontinuous. A subgroup preserving a local subring induces a continuous action on any
invariant embedded separable closure of a fixed residue subfield. Finite lifts of field
generators give an open subgroup contained in the inverse image of the fixing subgroup.

The base residue subfield is encoded by the injective field map `algebraMap k (ResidueField T)`.
The restricted automorphism of `T` is Mathlib's `RingEquiv.restrict`, and its action on the
residue field is `IsLocalRing.ResidueField.mapEquiv`; thus neither action is arbitrary.

Source: Stacks Project, Fields, Tag 0BMJ (`lemma-galois-profinite`), and
Fundamental Groups of Schemes, Tag 0BSW (`lemma-identify-inertia`).
(blueprint: lem-dl-a1-residue-action-krull-continuity)

Proof:
1. An F-automorphism is a K-automorphism fixing F. Under `fixingSubgroupEquiv`, the
   pointwise stabilizer of any finite subset of Ω corresponds to its intersection with
   F's fixing subgroup. These identical finite evaluation neighbourhoods give continuity
   in both directions, without any finiteness assumption on F/K. This is also the
   upstream `fixingSubgroupContinuousMulEquiv`.
2. Each g in Γ restricts to T, as does its inverse. Ring automorphisms preserve units
   and hence the maximal ideal of this local ring. They therefore induce residue
   automorphisms, satisfying q(g(z)) = gbar(q(z)). Invariance of the image of j, also
   for the inverse automorphism, gives r(g) = j⁻¹ gbar j on ks. Fixing k makes this a
   k-automorphism. Compatibility with composition gives the homomorphism r and the
   displayed characterization. Here j⁻¹ is only the inverse on the image of j.
3. The simultaneous stabilizer of the finitely many lifts z_i is a subgroup, open in
   Γ by the finite-evaluation neighbourhood basis. If g fixes z_i, then
   j(r(g)(a_i)) = q(g(z_i)) = q(z_i) = j(a_i). Injectivity of j implies that r(g)
   fixes every a_i, hence the intermediate field they generate. This gives containment
   in the inverse image of e's fixing subgroup.
4. For any finite subset A of ks, choose lifts in T of its image under j using
   surjectivity of the residue quotient. Their finite pointwise stabilizer is open and
   maps into the pointwise stabilizer of A. Translating at each g gives an open
   neighbourhood mapping into every basic Krull neighbourhood of r(g). Therefore r
   is continuous; no cofinality assertion about finite Galois subfields is needed.
-/
theorem residue_action_krull_continuity
    (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (F : IntermediateField K Ω) :
    (Continuous F.fixingSubgroupEquiv ∧ Continuous F.fixingSubgroupEquiv.symm) ∧
    ∀ (Γ : Subgroup (Ω ≃ₐ[K] Ω)) (T : Subring Ω) [IsLocalRing T]
      (hT : ∀ (g : Γ) (x : Ω), x ∈ T ↔ (g : Ω ≃ₐ[K] Ω) x ∈ T)
      (k : Type w) [Field k] [Algebra k (IsLocalRing.ResidueField T)]
      (ks : Type z) [Field ks] [Algebra k ks] [IsSepClosure k ks]
      (j : ks →ₐ[k] IsLocalRing.ResidueField T),
      (∀ (g : Γ) (a : k),
        IsLocalRing.ResidueField.mapEquiv
          ((g : Ω ≃ₐ[K] Ω).toRingEquiv.restrict T T (hT g))
          (algebraMap k (IsLocalRing.ResidueField T) a) =
            algebraMap k (IsLocalRing.ResidueField T) a) →
      (∀ g : Γ, Set.MapsTo
        (IsLocalRing.ResidueField.mapEquiv
          ((g : Ω ≃ₐ[K] Ω).toRingEquiv.restrict T T (hT g)))
        (Set.range j) (Set.range j)) →
      ∃ r : Γ →* (ks ≃ₐ[k] ks),
        (∀ (g : Γ) (a : ks), j (r g a) =
          IsLocalRing.ResidueField.mapEquiv
            ((g : Ω ≃ₐ[K] Ω).toRingEquiv.restrict T T (hT g)) (j a)) ∧
        Continuous r ∧
        ∀ (e : IntermediateField k ks) [FiniteDimensional k e] [IsGalois k e]
          (n : ℕ) (a : Fin n → e),
          IntermediateField.adjoin k (Set.range fun i ↦ (a i : ks)) = e →
          ∀ z : Fin n → T,
            (∀ i : Fin n, IsLocalRing.residue T (z i) = j (a i : ks)) →
            ∃ U : OpenSubgroup Γ,
              (∀ g : Γ, g ∈ U ↔ ∀ i : Fin n,
                (g : Ω ≃ₐ[K] Ω) (z i : Ω) = (z i : Ω)) ∧
              U.toSubgroup ≤ e.fixingSubgroup.comap r := by
  sorry

end IntermediateField
