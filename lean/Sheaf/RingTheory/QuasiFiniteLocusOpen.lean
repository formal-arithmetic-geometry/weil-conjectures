module

public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.RingTheory.QuasiFiniteAtPrime
import Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway
import all Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Openness of the quasi-finite locus for a finite-type ring map

Source: Stacks Project, Algebra, Lemma Tag 00QA, label `lemma-quasi-finite-open`
(blueprint: lem-weil-pbc-ring-quasi-finite-locus-open).
-/

@[expose] public section

universe u v

namespace Algebra

private theorem isQuasiFiniteAtPrime_comap_away
    (R : Type*) (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [FiniteType R S] (g : S)
    (q : PrimeSpectrum (Localization.Away g))
    (hq : IsQuasiFiniteAtPrime R (Localization.Away g) q) :
    IsQuasiFiniteAtPrime R S (q.comap (algebraMap S (Localization.Away g))) := by
  let i := PrimeSpectrum.comap (algebraMap S (Localization.Away g))
  let a := PrimeSpectrum.comap (algebraMap R S)
  let b := PrimeSpectrum.comap (algebraMap R (Localization.Away g))
  let F := a ⁻¹' {a (i q)}
  let G := b ⁻¹' {b q}
  have hsq : ∀ x, a (i x) = b x := by
    intro x
    exact congrArg (fun f ↦ x.comap f) (IsScalarTower.algebraMap_eq R S _).symm
  have hG : G = i ⁻¹' F := by
    ext x
    change b x = b q ↔ a (i x) = a (i q)
    rw [hsq x, hsq q]
  let e := Homeomorph.setCongr hG
  let k : G → F := (F.restrictPreimage i) ∘ e
  have hk : Topology.IsOpenEmbedding k :=
    ((PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away g) g).restrictPreimage
      F).comp e.isOpenEmbedding
  have hx : k ⟨q, rfl⟩ = ⟨i q, rfl⟩ := rfl
  apply (isQuasiFiniteAtPrime_iff_isOpen_fiber R S (i q)).mpr
  have ho := (isQuasiFiniteAtPrime_iff_isOpen_fiber R (Localization.Away g) q).mp hq
  simpa only [Set.image_singleton, hx] using
    (hk.isOpen_iff_image_isOpen (s := {⟨q, rfl⟩})).mp ho

/-- The quasi-finite locus of a finite-type ring map is open, and is locally
represented by localizations on which the map is quasi-finite at every prime.
Source: Stacks Project, Algebra, Lemma Tag 00QA
(blueprint: lem-weil-pbc-ring-quasi-finite-locus-open).

Proof (following Stacks Project, Algebra, Lemma Tag 00QA):
1. At a quasi-finite prime, the finite-subalgebra lemma supplies a finite
   `A`-subalgebra `B'` and `g ∉ q` with a bijective localized inclusion.
2. Mathlib's quasi-finite-algebra instances show that `B'_g` is quasi-finite
   over `A`. Surjectivity of the localized inclusion transfers this to `B_g`.
   Its fibre spectra are discrete, so every fibre point is isolated.
3. The fibre-spectrum homeomorphism identifies our predicate with openness of
   the distinguished singleton in the topological fibre of `Spec B → Spec A`.
4. The open embedding `Spec B_g → Spec B` restricts to an open embedding of
   these fibres. Its image of the distinguished singleton is the contracted
   singleton; thus quasi-finiteness descends to every point of `D(g)`.
5. Each quasi-finite point has such a basic open neighbourhood inside the locus.
   The basic-open basis gives openness, and step 2 gives the local characterization.
-/
theorem isOpen_isQuasiFiniteAtPrime (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] :
    IsOpen {q : PrimeSpectrum B | IsQuasiFiniteAtPrime A B q} ∧
      (IsOpen {q : PrimeSpectrum B | IsQuasiFiniteAtPrime A B q} ↔
        ∀ q : PrimeSpectrum B, IsQuasiFiniteAtPrime A B q →
          ∃ g : B, g ∉ q.asIdeal ∧
            ∀ p : PrimeSpectrum (Localization.Away g),
              IsQuasiFiniteAtPrime A (Localization.Away g) p) := by
  have hlocal : ∀ q : PrimeSpectrum B, IsQuasiFiniteAtPrime A B q →
      ∃ g : B, g ∉ q.asIdeal ∧
        ∀ p : PrimeSpectrum (Localization.Away g),
          IsQuasiFiniteAtPrime A (Localization.Away g) p := by
    intro q hq
    obtain ⟨B', hB', g, hg, hbij⟩ :=
      exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime A B q hq
    let := hB'
    have : QuasiFinite A (Localization.Away g) := inferInstance
    have : QuasiFinite A (Localization.Away g.1) :=
      QuasiFinite.of_surjective_algHom (Localization.awayMapₐ B'.val g) hbij.2
    refine ⟨g.1, hg, ?_⟩
    intro p
    unfold IsQuasiFiniteAtPrime
    exact isOpen_discrete _
  have hopen : IsOpen {q : PrimeSpectrum B | IsQuasiFiniteAtPrime A B q} := by
    apply PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mpr
    intro q hq
    obtain ⟨g, hg, hgp⟩ := hlocal q hq
    refine ⟨PrimeSpectrum.basicOpen g, ⟨g, rfl⟩, hg, ?_⟩
    intro q' hq'
    have hr : q' ∈ Set.range
        (PrimeSpectrum.comap (algebraMap B (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hq'
    obtain ⟨p, rfl⟩ := hr
    exact isQuasiFiniteAtPrime_comap_away A B g p (hgp p)
  exact ⟨hopen, ⟨fun _ ↦ hlocal, fun _ ↦ hopen⟩⟩

end Algebra
