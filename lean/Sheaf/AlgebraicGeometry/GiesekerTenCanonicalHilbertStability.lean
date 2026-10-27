module

public import Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter
public import Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization
import Sheaf.AlgebraicGeometry.StablePointedCurve
import Sheaf.AlgebraicGeometry.BalancedNodalTraitStableCanonicalLimit
import Sheaf.AlgebraicGeometry.GiesekerPotentialStability
import Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction
import Sheaf.AlgebraicGeometry.NoetherianImageBoundaryDvr
import Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices

/-! # Gieseker stability of the ten-canonical Hilbert locus

Source: Morrison, arXiv:0810.2340, §3.3, Proposition 10 and Corollary 11, pp.16--17,
with canonical multiple ten and the arbitrary-characteristic central descent in §2.1.
(blueprint: lem-sfb-gieseker-ten-canonical-hilbert-stability)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.TenCanonicalHilbert

/-- The same Hilbert representation in the Hilbert--Plücker interface. The only
transport is the equality of the two finite coordinate counts; the total scheme,
polynomial components and inclusions are retained. The universal ideal is pulled
back along the canonical projective-space base-change isomorphism.
Source: Morrison §2.1 and §3.3, Definition 9
(blueprint: lem-sfb-gieseker-ten-canonical-hilbert-stability). -/
def pluckerHilbert {k : Type u} [Field k] {g : ℕ} (H : Hilbert k g) (hg : 2 ≤ g) :
    HilbertPlucker.Hilbert k (19 * (g - 1) - 2) H.index := by
  have h : 19 * (g - 1) - 1 = (19 * (g - 1) - 2) + 1 := by omega
  let F (r : ℕ) :=
    (e : (properHilbertPresheaf
      (ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)) ↘ Spec (.of k))).RepresentableBy H.H) ×'
      ∀ (Q : NumericalHilbertPolynomial) (T : Over (Spec (.of k))) (b : T ⟶ H.H),
        HasProjectiveFibreHilbertPolynomial
          (ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)) ↘
            Spec (.of k))
          (𝟙 (ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)))) T (e.homEquiv b).1 Q.1 ↔
            ∃! a : T ⟶ H.HP Q, a ≫ H.inclusion Q = b
  let original : F (19 * (g - 1) - 1) := ⟨H.representation, H.component⟩
  let transported : F ((19 * (g - 1) - 2) + 1) := h ▸ original
  exact
    { total := H.H
      representation := transported.1
      components := H.HP
      inclusion := H.inclusion
      coproduct := H.coproduct
      projective := H.projective
      component := transported.2
      ideal := (transported.1.homEquiv (H.inclusion H.index)).1.comap
        (ProjectiveSpace.isPullback_map
          (HilbertPlucker.Coordinates (19 * (g - 1) - 2)) (H.HP H.index).hom).isoPullback.hom
      universal_ideal := rfl }

end AlgebraicGeometry.TenCanonicalHilbert

namespace AlgebraicGeometry

/-- In every characteristic the complete ten-canonical locus lies in the stable
Hilbert locus and is closed in the semistable locus, for every sufficiently high
Hilbert degree. The bound is chosen before the field and the representing data.
The Hilbert--Plücker presentation specifies the symmetric-power quotient, its
Plücker closed embedding, the ample determinant line raised to the positive power
r = 19(g - 1), its descended PGL linearization, and the stable and semistable opens.

Source: Morrison, arXiv:0810.2340, §3.3, Proposition 10 and Corollary 11, pp.16--17.
Proof plan, following the seven DAG steps:
1. Choose the uniform Hilbert, smooth-stability and potential-stability bounds.
   The Hilbert--Plücker theorem gives the quotient and descended linearization,
   preserving stability even in characteristics dividing r.
2. A trait semistable generically in J has a nodal prepared family. The balanced
   nodal trait limit theorem makes its special fibre stable and ten-canonical;
   the parameter theorem puts its point in J.
3. A boundary point would give a DVR by the Noetherian image-boundary lemma,
   contradicting step 2. An immersion with closed image is a closed immersion.
4. Framed trait smoothing deforms every geometric point of J to a smooth curve,
   whose high-degree Hilbert point is stable.
5. Semistable replacement, after DVR extension and a coordinate change, gives a
   second family. Step 3 makes it factor through J: its defining ideal vanishes
   in the fraction field and hence in the DVR.
6. Pluricanonical lattice comparison respects products; nodal canonical
   reconstruction identifies the two stable families as Proj of that algebra.
   Their special complete frames differ by PGL, so the original point is
   semistable. Field-extension compatibility gives all of J in the semistable
   locus, and step 3 gives the asserted closed immersion.
7. Stabilizers identify with stable-curve automorphism schemes and are finite
   by stable-pointed Isom finiteness. In the closed invariant J, an orbit boundary
   would have smaller dimension, whereas every orbit has dimension dim PGL.
   Every orbit is therefore closed in the semistable locus, proving stability.
(blueprint: lem-sfb-gieseker-ten-canonical-hilbert-stability). -/
theorem gieseker_ten_canonical_hilbert_stability (g : ℕ) (hg : 2 ≤ g) :
    ∃ M : ℕ, ∀ (k : Type u) [Field k] (D : TenCanonicalHilbert.Presentation k g)
      (m : ℕ), M ≤ m →
      ∃ E : HilbertPlucker.Presentation (TenCanonicalHilbert.pluckerHilbert D.hilbert hg) m,
        (∀ z : D.J.left, D.inclusion.left z ∈ E.stable) ∧
        ∃ j : D.J.left ⟶ E.semistable.toScheme,
          j ≫ E.semistable.ι = D.inclusion.left ∧ IsClosedImmersion j := by
  sorry

end AlgebraicGeometry
