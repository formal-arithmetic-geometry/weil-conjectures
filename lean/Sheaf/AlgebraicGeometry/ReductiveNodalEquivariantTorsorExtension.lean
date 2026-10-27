module

public import Sheaf.AlgebraicGeometry.NodalTorusChart
public import Sheaf.AlgebraicGeometry.EquivariantRepresentedRightTorsor
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Extension of reductive equivariant torsors across the nodal origin

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto
Decompositions, Section 2, Claim 2, printed p.2; Section 3, proof of
Theorem 1.3, (1) implies (2), printed p.6
(blueprint: lem-sfb-reductive-nodal-equivariant-torsor-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every equivariant right torsor under a reductive DVR group extends to the nodal chart.
The cartesian equivariant arrow identifies its restriction with the original torsor.
Source: AHLH, Section 2, Claim 2, p.2; Section 3, Theorem 1.3, (1) implies (2), p.6
(blueprint: lem-sfb-reductive-nodal-equivariant-torsor-extension).

Proof plan:
1. By lem-sfb-dvr-reductive-linear-affine-quotient embed H in GL_n with affine quotient.
   Apply lem-sfb-linear-torsor-reduction-sections to obtain its extended-structure-group
   torsor E, bundle V and reduction section σ. Naturality gives the commuting torus action.
2. By lem-sfb-nodal-surface-flat-hartogs the chart is a regular integral Noetherian surface
   and the origin has codimension two. Apply lem-sfb-regular-surface-vector-bundle-extension
   to extend V as j_*V. Projection G_m × X → X is flat; action differs from projection by
   the automorphism (z,x) ↦ (z,zx). Flat Hartogs extends the two bundle pullback maps and
   their inverses uniquely. Injectivity on Hom on X and G_m² × X proves the unit and
   cocycle laws. The frame equivalence gives the equivariant extended GL_n-torsor.
3. Its quotient by H is affine. Flat Hartogs extends σ uniquely, first over X and then
   over G_m × X; uniqueness there proves equivariance of the extended section.
4. Pull back the extended GL_n-torsor along this section. The reduction equivalence makes
   this a represented right H-torsor. The invariant section gives the commuting torus
   action, and base-change naturality gives the cartesian equivariant identification
   over U. None of these steps requires completeness, splitness or perfect residue field. -/
theorem exists_reductive_nodal_equivariant_torsor_extension
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) (H : Grp (Over (Spec (.of A))))
    [Smooth H.X.hom] [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (hred : ∀ (k : Type u) [Field k] (b : Spec (.of k) ⟶ Spec (.of A)),
      ReductiveTorusCentralizer.IsReductive ((Over.pullback b).mapGrp.obj H))
    (P : EquivariantRepresentedRightTorsor (NodalTorusChart.torus A) H
      (NodalTorusChart.openChart A π)) :
    ∃ Q : EquivariantRepresentedRightTorsor (NodalTorusChart.torus A) H
        (NodalTorusChart.chart A π),
      Nonempty (EquivariantRepresentedRightTorsor.RestrictionIso
        (NodalTorusChart.inclusion A π) P Q) := by
  sorry

end AlgebraicGeometry
