module

public import Sheaf.AlgebraicGeometry.GroupScheme.ValuativelyBoundedPoints
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Sheaf.AlgebraicGeometry.GroupScheme.SplitReductiveDVRCartanDecomposition

/-! # Maximal boundedness of integral points of a split reductive model

Source: Prasad--Yu, On quasi-reductive group schemes, Lemma 3.7, first assertion,
and Proposition 4.3, second paragraph, pp.7--8
(blueprint: lem-sfb-split-reductive-integral-maximal-bounded).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace AlgebraicGeometry

/-- Integral points of a split reductive model over a henselian DVR with algebraically
closed residue field form a maximal bounded subgroup of its generic points.

Source: Prasad--Yu, Lemma 3.7, first assertion, and Proposition 4.3, pp.7--8
(blueprint: lem-sfb-split-reductive-integral-maximal-bounded).

Proof plan:
1. Write D = Spec A. By def-weil-affine-spectrum and
   lem-weil-pbc-fibre-product-affine-spectra, the generic coordinate ring is
   A tensor_R L = (R minus zero) inverse A. Write f = a/s. On integral points,
   a evaluates in R, giving the bound -v(s), including zero evaluations.
   Generic restriction is injective since R embeds in its fraction field L.
2. For a bounded subgroup M containing the integral subgroup K, write m = k1 t k2
   by lem-sfb-split-reductive-dvr-cartan-decomposition. Thus t and every positive
   power t^n lie in M.
3. The closed immersion of the split torus makes A → R[z_j, z_j inverse]
   surjective (def-weil-closed-immersion). Lift each coordinate and its inverse
   to A. Their values on t^n have valuations n v(a_j) and -n v(a_j).
   Boundedness forces v(a_j) = 0, since otherwise one sequence has no lower bound.
   Only lifts as regular functions are needed, not characters of the whole group.
4. By def-sc-discrete-valuation-ring every a_j is a unit of R. Hence t is integral,
   so m is integral and M = K. For rank zero the coordinate list is empty and
   the torus point is the identity. No completeness or local compactness is used. -/
theorem splitReductive_integral_maximal_bounded
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (L : Type u) [Field L] [Algebra R L] [IsFractionRing R L]
    (v : AddValuation L (WithTop ℤ))
    (hv : ∀ a : R, v (algebraMap R L a) =
      WithTop.map (fun n : ℕ ↦ (n : ℤ)) (IsDiscreteValuationRing.addVal R a))
    (D T : Grp (Over (Spec (.of R))))
    [Smooth D.X.hom] [IsAffine D.X.left]
    [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    (i : T ⟶ D) [IsClosedImmersion i.hom.hom.left]
    (r : ℕ) (e : T ≅ RingGroupSchemes.splitTorus R r)
    (hred : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : R →+* Ω),
      ReductiveTorusCentralizer.IsReductive
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj D))
    (hmax : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : R →+* Ω),
      ReductiveTorusCentralizer.IsMaximalTorus
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map i)) :
    ValuativelyBoundedPoints.IsBounded R L D v
      (ValuativelyBoundedPoints.integralPoints R L D) ∧
    ∀ M : Subgroup (ValuativelyBoundedPoints.genericPoints R L D),
      ValuativelyBoundedPoints.IsBounded R L D v M →
      ValuativelyBoundedPoints.integralPoints R L D ≤ M →
      M = ValuativelyBoundedPoints.integralPoints R L D := by
  sorry

end AlgebraicGeometry
