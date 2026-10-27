module

public import Mathlib.FieldTheory.Galois.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends

/-!
# Descent of a Galois-invariant clopen partition

Source: Stacks Project, Varieties, Tag 038B (`lemma-closed-fixed-by-Galois`) and
Tag 038C (`lemma-tricky`), the clopen-partition descent following the intersection/union.
(blueprint: lem-trf-galois-invariant-clopen-partition-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nonempty two-part clopen partition invariant under every Galois automorphism
of a scalar extension descends to a unique ordered nonempty clopen partition.
No finiteness, connectedness or quasi-compactness is required.

Source: Stacks Project, Varieties, Tags 038B and 038C
(blueprint: lem-trf-galois-invariant-clopen-partition-descent).

Proof: The spectrum map of a field extension is surjective
(lem-pc-field-extension-surjective); its pullback projection is surjective by
lem-weil-pbc-surjective-base-change. Apply
lem-weil-pbc-galois-invariant-closed-subset-descends separately to the closed invariant
sets P and Q, obtaining closed sets P₀ and Q₀ with the prescribed inverse images.
For each x of X choose a lift y along the surjective projection. Membership in P₀
and Q₀ is equivalent to membership of y in P and Q respectively. Thus P₀ and Q₀
are disjoint and cover X. Each is the complement of the other closed set, hence
both are clopen. A point of P maps to P₀, and a point of Q maps to Q₀, proving
nonemptiness. For any other pair with the same inverse images, the same lift of
each x tests membership in each coordinate, giving equality of both subsets and
therefore uniqueness of the ordered pair. -/
theorem existsUnique_clopen_partition_of_galois_invariant
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (P Q : Set ↥(pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
    (hPne : P.Nonempty) (hQne : Q.Nonempty)
    (hP : IsClopen P) (hQ : IsClopen Q)
    (hdisjoint : Disjoint P Q) (hcover : P ∪ Q = Set.univ)
    (hPinvariant : ∀ σ : L ≃ₐ[k] L,
      (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' P = P)
    (hQinvariant : ∀ σ : L ≃ₐ[k] L,
      (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' Q = Q) :
    ∃! R : Set X × Set X,
      R.1.Nonempty ∧ R.2.Nonempty ∧ IsClopen R.1 ∧ IsClopen R.2 ∧
      Disjoint R.1 R.2 ∧ R.1 ∪ R.2 = Set.univ ∧
      (pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹' R.1 = P ∧
      (pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹' R.2 = Q := by
  let p := pullback.fst (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  have hp : Function.Surjective p := p.surjective
  obtain ⟨A, hAclosed, hApre⟩ :=
    exists_closed_subset_of_galois_invariant k L X P hP.isClosed hPinvariant
  obtain ⟨B, hBclosed, hBpre⟩ :=
    exists_closed_subset_of_galois_invariant k L X Q hQ.isClosed hQinvariant
  change p ⁻¹' A = P at hApre
  change p ⁻¹' B = Q at hBpre
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    obtain ⟨y, rfl⟩ := hp x
    apply Set.disjoint_left.mp hdisjoint
    · rw [← hApre]
      exact hxA
    · rw [← hBpre]
      exact hxB
  have hABcover : A ∪ B = Set.univ := by
    apply hp.preimage_injective
    simpa only [Set.preimage_union, Set.preimage_univ, hApre, hBpre] using hcover
  have hAcB : Aᶜ = B := by
    ext x
    constructor
    · intro hx
      have hxcover : x ∈ A ∪ B := by rw [hABcover]; trivial
      exact hxcover.resolve_left hx
    · intro hxB hxA
      exact Set.disjoint_left.mp hAB hxA hxB
  have hBcA : Bᶜ = A := by rw [← hAcB, compl_compl]
  have hAne : A.Nonempty := by
    obtain ⟨y, hy⟩ := hPne
    refine ⟨p y, ?_⟩
    change y ∈ p ⁻¹' A
    rwa [hApre]
  have hBne : B.Nonempty := by
    obtain ⟨y, hy⟩ := hQne
    refine ⟨p y, ?_⟩
    change y ∈ p ⁻¹' B
    rwa [hBpre]
  refine ⟨(A, B), ⟨hAne, hBne, ⟨hAclosed, ?_⟩, ⟨hBclosed, ?_⟩,
    hAB, hABcover, hApre, hBpre⟩, ?_⟩
  · exact hBcA ▸ hBclosed.isOpen_compl
  · exact hAcB ▸ hAclosed.isOpen_compl
  · intro R hR
    apply Prod.ext
    · exact hp.preimage_injective (hR.2.2.2.2.2.2.1.trans hApre.symm)
    · exact hp.preimage_injective (hR.2.2.2.2.2.2.2.trans hBpre.symm)

end AlgebraicGeometry
