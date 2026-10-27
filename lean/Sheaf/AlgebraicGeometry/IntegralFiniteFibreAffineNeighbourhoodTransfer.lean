module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget

/-!
# Affine neighbourhood transfer under integral finite-fibre surjections

Source: Anantharaman, Schémas en groupes, espaces homogènes et espaces algébriques sur une
base de dimension 1, Proposition 4.1.3 (OCR 4.1.5), printed p.55; Raynaud, Un critère
 d'effectivité de descente, Corollary 3.8, printed p.15
(blueprint: lem-sfb-integral-finite-fibre-affine-neighbourhood-transfer).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An integral surjection with finite underlying fibres onto a locally Noetherian scheme
transfers the existence of a common affine open neighbourhood of a finite set and its entire
inverse image. Source: Anantharaman, Proposition 4.1.3 (OCR 4.1.5), printed p.55;
Raynaud, Corollary 3.8, printed p.15
(blueprint: lem-sfb-integral-finite-fibre-affine-neighbourhood-transfer).

Proof:
1. For the empty set use the empty affine open, Spec of the zero ring. In general, integrality
   makes q affine, so the preimage of an affine open containing E is affine and contains its
   entire inverse image (lem-weil-pbc-affine-morphism-permanence).
2. Conversely, for nonempty E choose an affine V = Spec A containing E' = q⁻¹(E). Surjectivity
   and finite fibres make E' finite and nonempty. Z is quasi-separated by local Noetherianity,
   and Y is quasi-separated since q is affine (lem-weil-pbc-locally-noetherian-quasi-separated,
   lem-weil-pbc-qcqs-morphism-permanence). Localize A away from the union of the primes in E'.
3. The image H' of that localization F' is exactly the union of the generalizations of E':
   a prime disjoint from the multiplicative set lies in one of those finitely many primes,
   by finite prime avoidance (lem-weil-pbc-localization-spectrum-embedding,
   lem-weil-pbc-prime-avoidance). All these generalizations lie in V.
4. The map F' → V is flat and a monomorphism by
   lem-sfb-localization-spectrum-flat-monomorphism. Composing with the open immersion into Y
   preserves these properties; the composite is quasi-compact since F' is affine and Y is
   quasi-separated (def-weil-open-immersion, def-weil-flat-morphism,
   lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence).
5. Let H be the union of the generalizations of E. Then q⁻¹(H) = H'. Continuity gives one
   inclusion; for the other, q is closed by integrality. If q(y) generalizes e, the closed
   image of the closure of y contains e, so y specializes to a point of E'
   (pqf-lem-integral-univclosed, def-weil-proper-morphism).
6. Apply lem-sfb-integral-descent-flat-monomorphism-subset to descend F' → Y to a
   quasi-compact flat monomorphism F → Z with image H and F' ≅ Y ×_Z F.
7. F' → F is surjective and universally closed by base change from q
   (lem-weil-pbc-surjective-base-change, pqf-lem-integral-univclosed). Since F' is affine,
   lem-weil-pbc-surjective-universally-closed-affine-target makes F affine.
8. The quasi-affine neighbourhood theorem applied to F → Z gives a quasi-compact quasi-affine
   open containing H and hence E (lem-sfb-flat-monomorphism-quasiaffine-neighbourhood).
9. Present this open as an open W of Spec B, with closed complement V(J). Finite prime
   avoidance gives b ∈ J outside all primes of E; the affine principal open D(b) lies in W
   and contains E. Transport it to Z (lem-weil-pbc-prime-avoidance,
   lem-weil-pbc-affine-ideals-closed-subscheme, def-weil-affine-spectrum).
-/
theorem exists_affineOpen_iff_preimage_of_integral_surjective_finite_fibres
    {Y Z : Scheme.{u}} [IsLocallyNoetherian Z] (q : Y ⟶ Z)
    [IsIntegralHom q] [Surjective q]
    (hfinite : ∀ z : Z, (q ⁻¹' {z}).Finite) (E : Set Z) (hE : E.Finite) :
    (∃ U : Z.Opens, IsAffineOpen U ∧ E ⊆ (U : Set Z)) ↔
      ∃ V : Y.Opens, IsAffineOpen V ∧ q ⁻¹' E ⊆ (V : Set Y) := by
  sorry

end AlgebraicGeometry
