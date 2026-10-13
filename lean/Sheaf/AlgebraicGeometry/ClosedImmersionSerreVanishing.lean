module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre

/-! # Serre vanishing for the restricted projective-space twists -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Serre vanishing for a finitely presented quasi-coherent module on a closed subscheme
of finite-dimensional projective space over a Noetherian ring.
Source: Stacks Project, Cohomology of Schemes, Tags 01YS and 0B5T (4).
(blueprint: lem-weil-pbc-closed-immersion-serre-vanishing)

Proof: Projective space is locally Noetherian, and its closed subscheme X is locally
Noetherian. Hence F and i_*F are coherent. For G = i_*F, choose an epimorphism from a
finite direct sum of negative twists to G; its kernel is coherent. The standard affine
cover by N+1 opens computes quasi-coherent cohomology, and gives vanishing above degree N.
Descend in cohomological degree, for all coherent G at once. Tensor the epimorphism and
its kernel sequence by O(t), which is invertible and therefore preserves exactness.
Positive-degree cohomology of each summand O(t-a) vanishes once t is sufficiently large;
this follows from the monomial Cech computation of nonnegative twists, valid over any
base ring. The next-degree cohomology of the twisted kernel vanishes for large t by the
induction hypothesis. The long exact sequence therefore kills the given-degree
cohomology of G(t). There are only finitely many relevant positive degrees, so take the
maximum of their bounds and zero. The projection formula identifies i_*(F tensor i^*O(t))
with G(t), and the affine-morphism cohomology comparison for the closed immersion i
identifies its cohomology with that on X. This gives one natural-number bound for all
positive degrees. No arbitrary ample module or residue-class argument is used here. -/
theorem exists_isZero_moduleCohomology_tensor_twist_of_closedImmersion
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ∃ t₀ : ℕ, ∀ (p t : ℕ), 0 < p → t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (tensorObj F (ProjectiveSpace.twistRestrict i t))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
