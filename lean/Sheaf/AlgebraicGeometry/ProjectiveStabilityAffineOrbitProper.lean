module

public import Sheaf.AlgebraicGeometry.ProjectiveRepresentationLinearization
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.ProjectiveSpace.PicardPn
import Sheaf.AlgebraicGeometry.ProjectivePolarizationSectionAlgebra
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Projective stability and the proper affine vector orbit morphism

Source: MFK, Geometric Invariant Theory, Chapter 2, §1, Proposition 2.2;
Morrison, arXiv:0810.2340, §2.2, Proposition 1, pp.6--7.
(blueprint: lem-sfb-projective-stability-affine-orbit-proper)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.ProjectiveRepresentation

/-- The affine-cone criterion for proper stability, in every characteristic, with the full
scheme-theoretic stabilizer, including infinitesimal stabilizers and nonreduced Y.
Source: MFK, Chapter 2, §1, Proposition 2.2 and Theorem 2.1; Morrison §2.2, Proposition 1.
(blueprint: lem-sfb-projective-stability-affine-orbit-proper)

Proof (the nine steps of the DAG):
1. Choose bases. SL is smooth connected affine reductive (lem-sfb-special-linear-reductive).
   Projectivity gives separated finite type (lem-kun-projective-implies-proper).
   sk-thm-picard-pn identifies homogeneous polynomials with sections; the dual tautological
   convention makes their transformation the inverse substitution.
2. Given a stable point and invariant s nonzero there, a sufficiently large power lifts to
   polynomials by lem-sfb-projective-polarization-section-algebra. Apply
   lem-sfb-haboush-symmetric-power-lift to the inverse image of the invariant line to obtain
   an invariant homogeneous f of positive degree with f(v)=c nonzero. This uses no exactness
   of invariants, and therefore works also in positive characteristic and for nonreduced Y.
3. The invariant slice T=Spec(P/(I,f-c)) maps finite locally freely and surjectively to Y_f
   by lem-sfb-homogeneous-slice-finite-cover. The projective orbit is closed in Y_f.
4. In the inverse image of that orbit every vector stabilizer is dimension zero, by
   lem-sfb-zero-dimensional-stabilizer-finite-orbit. All its orbits have dimension dim G.
   lem-sfb-smooth-group-orbit-geometry forces the vector orbit to be closed: a nonempty
   boundary would have a k-point (lem-wf-affine-nullstellensatz-vanishing), and that point's
   orbit would have strictly smaller dimension.
5. By lem-sfb-zero-dimensional-stabilizer-finite-orbit the orbit map to the closed reduced
   orbit is finite locally free. Compose with its closed immersion using
   lem-weil-pbc-closed-immersion-finite and lem-weil-pbc-finite-composition. It is finite,
   hence proper by lem-weil-pbc-finite-closed-map-finite-fibres.
6. Conversely, properness and affineness imply finiteness (lem-sfb-affine-proper-finite,
   lem-weil-pbc-morphism-affine-schemes-affine). The vector orbit is closed, avoids zero,
   and its stabilizer has finitely many k-points (lem-weil-pbc-finite-closed-map-finite-fibres,
   lem-wf-affine-nullstellensatz-vanishing). Give the orbit its reduced closed structure.
7. Separate it from zero by a function in the origin ideal restricting to 1. Choose a finite
   rational subrepresentation containing this function (lem-sfb-comodule-finite-subrepresentation).
   Haboush's lift produces an invariant function restricting to 1. One positive homogeneous
   component f is nonzero at v, proving semistability.
8. The finite slice map is closed, so the projective orbit is closed in Y_f. For its projective
   stabilizer, gv=t(g)v and t(g)^deg(f)=1. Its kernel is the finite vector stabilizer and its
   image has at most deg(f) points. Thus the full stabilizer has dimension zero by
   lem-sfb-zero-dimensional-stabilizer-finite-orbit, without assuming smoothness.
9. For any positive-degree invariant s of degree e and evaluation b at v, the section
   c^e s^d-b^d f^e vanishes on the orbit and hence its closure. At a boundary point where
   f=0 all such s vanish, so that boundary misses the semistable locus. Thus the orbit is
   closed in the entire semistable locus, completing the converse. -/
theorem stable_iff_vectorOrbit_proper
    (k : Type u) [Field k] [IsAlgClosed k]
    (E : Type u) [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (hr : 2 ≤ Module.finrank k E)
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (idx : Type u) [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
    (ρ : LinearGroupSchemes.specialLinear k (Module.finrank k E) ⟶ GeneralLinearGroup idx k)
    [IsMonHom ρ]
    (Y : Over (Spec (.of k))) [IsHProjective Y.hom]
    (j : Y ⟶ (ℙ(idx; Spec (.of k))).asOver (Spec (.of k))) [IsClosedImmersion j.left]
    (D : LinearizedEmbedding (G := ⟨LinearGroupSchemes.specialLinear k (Module.finrank k E)⟩)
      ρ j)
    (y : PGLLinearization.fieldTest k k ⟶ Y) (v : V) (hv : v ≠ 0)
    (hlift : IsVectorLift b j y v) :
    D.linearization.IsStable k y ↔
      IsProper (vectorOrbit (G := ⟨LinearGroupSchemes.specialLinear k (Module.finrank k E)⟩)
        b ρ v) := by
  sorry

end AlgebraicGeometry.ProjectiveRepresentation
