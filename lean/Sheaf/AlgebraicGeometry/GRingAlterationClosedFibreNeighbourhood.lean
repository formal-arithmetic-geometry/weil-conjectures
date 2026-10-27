module

public import WeilConjectures.RingTheory.GRing
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Topology.Constructible
import WeilConjectures.Topology.ProconstructibleClosureSpecialization

/-!
# Alteration neighbourhoods regular over a closed fibre

Source: Kurano--Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Lemma 4.4, printed pp. 5--6, and Definition 3.2, printed p. 3
(blueprint: lem-per-g-ring-alteration-closed-fibre-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A G-ring domain with J-2 quotient admits, near each prime, an alteration covering whose
ambient stalks above the closed fibre are regular local.

Generic finiteness is expressed by finiteness of the canonical stalk map at a generic
point. Dominance (respectively surjectivity) makes its image the target's generic point;
these two stalks are therefore precisely the two function fields. No auxiliary field
extension or arbitrary algebra structure is chosen.

Source: Kurano--Shimomoto, Lemma 4.4 and Definition 3.2
(blueprint: lem-per-g-ring-alteration-closed-fibre-neighbourhood).

Proof:
1. Set A = B_q. The primes-of-localization and iterated-localization identifications
   (lem-weil-pbc-primes-of-localization, lem-weil-pbc-localize-localization-at-prime)
   identify every prime completion map with that of B, so A is a G-ring. It is a local
   Noetherian domain by lem-weil-pbc-localization-noetherian. Apply
   lem-per-semilocal-g-ring-j2 to obtain quasi-excellence, without universal catenarity.
2. Apply lem-per-qe-weak-uniformization-cover to Spec A to obtain regular integral
   Noetherian covering members and the proper surjective generically finite witness.
3. Spread the entire finite diagram by lem-per-local-alteration-diagram-spreading
   to Spec B[1/a], retaining integral Noetherian models and every morphism property.
4. Every point above a generalization of q has the same ambient stalk after base
   change to B_q: the inverted elements are already units in that stalk. Use
   lem-weil-pbc-affine-open-stalk-localization to identify these fraction rings.
   Thus all these ambient stalks are regular.
5. Finite-type composition (lem-sfb-finite-type-composition-base-change) permits
   lem-per-j2-closed-fibre-regular-locus to be applied over B. Each nonregular locus
   W_i above V(J) is closed and hence constructible (def-weil-constructible-subset).
6. The base is Noetherian by lem-weil-pbc-localization-noetherian. Finite type is
   locally finite presentation by lem-weil-pbc-finite-type-noetherian-finite-presentation.
   Apply lem-weil-pbc-chevalley-constructible-image using the affine qcqs property
   (lem-weil-pbc-affine-scheme-qcqs) to make every image E_i constructible.
7. The base is spectral by lem-weil-pbc-qcqs-scheme-spectral. If q were in the closure
   of E_i, lem-weil-pbc-spectral-proconstructible-closure-specialization would give
   a generalization in E_i. This contradicts the stalk regularity in step 4.
8. By lem-weil-pbc-spec-localization-away-basic-open choose a principal neighbourhood
   D(b) of q inside D(a) avoiding all finitely many closures. Restrict the diagram;
   the permanence clause of lem-per-local-alteration-diagram-spreading retains every
   property. Its bad loci are empty, and open restriction preserves the ambient stalks.
-/
theorem exists_gRing_alteration_closed_fibre_neighbourhood
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (hB : IsGRing B) (J q : Ideal B) [q.IsPrime]
    (hJ : ∀ (D : Type u) [CommRing D] [Algebra (B ⧸ J) D]
      [Algebra.FiniteType (B ⧸ J) D],
      IsOpen {r : PrimeSpectrum D | IsRegularLocalRing (Localization.AtPrime r.asIdeal)}) :
    ∃ b : B, b ∉ q ∧
      ∃ (n : ℕ) (X : Fin n → Scheme.{u})
        (φ : ∀ i : Fin n, X i ⟶ Spec (.of (Localization.Away b))),
        (∀ i : Fin n, IsIntegral (X i) ∧ IsNoetherian (X i) ∧
          DenseRange (φ i) ∧ LocallyOfFiniteType (φ i) ∧ QuasiCompact (φ i) ∧
          (∃ η : X i, IsGenericPoint η Set.univ ∧ ((φ i).stalkMap η).hom.Finite) ∧
          ∀ x : X i,
            Ideal.map (algebraMap B (Localization.Away b)) J ≤ (φ i x).asIdeal →
              IsRegularLocalRing ((X i).presheaf.stalk x)) ∧
        ∃ (V : Scheme.{u}) (p : V ⟶ Spec (.of (Localization.Away b))),
          IsIntegral V ∧ IsNoetherian V ∧ IsProper p ∧ Surjective p ∧
          (∃ η : V, IsGenericPoint η Set.univ ∧ (p.stalkMap η).hom.Finite) ∧
          ∃ (U : Fin n → V.Opens) (h : ∀ i : Fin n, (U i).toScheme ⟶ X i),
            (⨆ i : Fin n, U i) = ⊤ ∧ ∀ i : Fin n, h i ≫ φ i = (U i).ι ≫ p := by
  sorry

end AlgebraicGeometry
