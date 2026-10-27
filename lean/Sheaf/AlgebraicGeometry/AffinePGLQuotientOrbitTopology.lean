/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover
public import Sheaf.AlgebraicGeometry.AffineActionStackPresentation
public import Mathlib.RingTheory.FiniteType
import Sheaf.RepresentationTheory.PGLGeometricReductivity
import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.Topology.Separation.Basic

/-! # Topology and field extension of affine PGL invariant quotients

Source: Alper, arXiv:1005.2398v3, Theorems 9.1.4, 9.7.6, 5.3.1, 6.3.3 and
Proposition 5.2.9; Milne, Algebraic Groups, Propositions 7.4--7.6.
(blueprint: lem-sfb-affine-pgl-quotient-orbit-topology)

The invariant ring and quotient arrow are the recorded coordinate equalizer and Spec
of its inclusion. Geometric orbits are images of whole orbit schemes, including their
nonclosed points. Extended invariants use the actual pulled-back action diagram.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.SchemeAction

variable (k E : Type u) [Field k] [CommRing E] [Algebra k E]
variable (G : Over (Spec (.of k))) [GrpObj G] [ModObj G (affineActionScheme k E)]

/-- The algebra structure on the existing equalizer, given by its recorded constants.
Source: Alper, Remark 9.1.5 (blueprint: lem-sfb-affine-pgl-quotient-orbit-topology). -/
instance affineInvariantAlgebra : Algebra k (affineInvariants k E G) :=
  (affineInvariantConstants k E G).toAlgebra

/-- Invariants after extension are the equalizer on global sections of the two
pulled-back arrows. The canonical monoidal pullback comparison identifies this with
the action and projection for G_K acting on U_K; no abstract-point action is substituted.
Source: Alper, Proposition 5.2.9
(blueprint: lem-sfb-affine-pgl-quotient-orbit-topology). -/
def extendedAffineInvariants (K : Type u) [Field K] [Algebra k K] :
    Subring Γ(((Over.pullback (ProjectiveMatrixCentralCover.extension k K)).obj
      (affineActionScheme k E)).left, ⊤) :=
  RingHom.eqLocus
    (((Over.pullback (ProjectiveMatrixCentralCover.extension k K)).map
      (ModObj.smul (M := G) (X := affineActionScheme k E))).left.appTop.hom)
    (((Over.pullback (ProjectiveMatrixCentralCover.extension k K)).map
      (snd G (affineActionScheme k E))).left.appTop.hom)

/-- The full topological orbit of an Ω-point inside U_Ω. The source is Ω ×_k G,
and the two components of the arrow to U ×_k Ω are the action on x and projection.
Source: Milne, Propositions 7.4--7.6
(blueprint: lem-sfb-affine-pgl-quotient-orbit-topology). -/
def affineGeometricOrbit (Ω : Type u) [Field Ω] [Algebra k Ω]
    (x : affineActionScheme k Ω ⟶ affineActionScheme k E) :
    Set (affineActionScheme k E ⊗ affineActionScheme k Ω).left :=
  Set.range (lift
    (lift (snd (affineActionScheme k Ω) G) (fst (affineActionScheme k Ω) G ≫ x) ≫
      ModObj.smul (M := G) (X := affineActionScheme k E))
    (fst (affineActionScheme k Ω) G)).left

/-- Finite generation, surjectivity, invariant closed images, a unique closed orbit
in each geometric fibre, and the canonical field-extension comparison of invariant
quotients and their closed images. Closedness and closure of the geometric orbits
are taken inside U_Ω: the fibre over an Ω-rational point of Y_Ω is closed there,
so these are exactly closedness and closure in that fibre.

Source: Alper, Theorems 9.1.4, 9.7.6, 5.3.1 and 6.3.3, Proposition 5.2.9;
Milne, Propositions 7.4--7.6; Stacks Tags 00HD, 04XH, 01J3.
(blueprint: lem-sfb-affine-pgl-quotient-orbit-topology).

Proof, following all six steps of the DAG:
1. Put A = E^G. Apply lem-sfb-pgl-geometric-reductivity for finite generation and
power lifting. The smooth affine action-stack presentation and
lem-sfb-power-lifting-adequate-affine-quotient make [U/G] -> Spec A adequate.
Adequate-moduli surjectivity and the surjective smooth atlas make p surjective,
using lem-sfb-adequate-moduli-topological-images and
lem-sfb-smooth-presentation-closed-subsets.
2. Tensor 0 -> A -> E -> E tensor k[G] (the last map is the coaction difference)
with K. Every vector space is flat (lem-weil-pbc-module-over-field-flat), so
lem-weil-pbc-flat-tensor-exact identifies K tensor A with the extended equalizer.
Multiplication and the two pure-tensor formulas specify the canonical ring isomorphism.
Taking Spec identifies its quotient arrow with the pullback of p. The matrix central
cover commutes with field extension, so step 1 also applies over K.
3. The invariant closed D descends through the atlas to a reduced closed substack,
by lem-sfb-smooth-presentation-closed-subsets. Adequate-moduli closedness shows p(D)
is closed. The intersection-of-images assertion gives p(D1) intersect p(D2) =
p(D1 intersect D2), also over every extension by step 2.
4. For y over algebraically closed Ω the nonempty fibre is affine finite type over Ω.
The point y is closed in Y_Ω, since its coordinate map contains the constants.
Every nonempty closed subset of the fibre has a closed rational point by
lem-sc-quasi-compact-kolmogorov-closed-point and
lem-weil-pbc-closed-point-residue-field-base, applied to its reduced induced closed
subscheme (lem-weil-pbc-reduced-induced-closed-subscheme). The smooth-group orbit lemma
makes orbits locally closed with invariant closures and boundaries of smaller orbit
dimension. In any orbit closure choose an orbit of minimum dimension. Its boundary,
if nonempty, has a rational point and hence an orbit of smaller dimension, a contradiction.
Thus every orbit closure contains an orbit closed in the fibre.
5. Distinct closed orbits are disjoint: an intersection has a rational point by the
same closed-point lemmas; the surjective finite-type orbit maps have rational points
in their fibres, so both orbits are translates of that point. Step 3's intersection
formula forbids disjoint closed orbits over y. Thus the closed orbit is unique and,
by step 4 inside each closure, lies in every orbit closure.
6. Give D its reduced induced closed structure. Its base change has underlying subset
D_K, even if nonreduced. The image/base-change formula of Tag 04XH applied to D_red -> Y
and Y_K -> Y gives exactly p_K(D_K) = inverse-image(p(D)). Step 2 identifies p_K with
the extended invariant quotient. No step assumes reduced U, reduced stabilizers, or
invertibility of r or any characteristic. -/
theorem affine_pgl_quotient_orbit_topology
    (r : ℕ) (hr : 2 ≤ r) (H : Grp (Over (Spec (.of k))))
    (π : GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k ⟶ H.X)
    (j : StandardGroupSchemes.roots k r ⟶ LinearGroupSchemes.specialLinear k r)
    (_hP : ProjectiveMatrixCentralCover.Presentation k r hr H π j)
    [ModObj H.X (affineActionScheme k E)] [Algebra.FiniteType k E] :
    Algebra.FiniteType k (affineInvariants k E H.X) ∧
    Surjective (affineInvariantProjection k E H.X).left ∧
    (∀ D : Set (affineActionScheme k E).left, IsClosed D →
      (ModObj.smul (M := H.X) (X := affineActionScheme k E)).left ⁻¹' D =
        (snd H.X (affineActionScheme k E)).left ⁻¹' D →
      IsClosed ((affineInvariantProjection k E H.X).left '' D)) ∧
    (∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (y : affineActionScheme k Ω ⟶ affineInvariantSpectrum k E H.X),
      ∃ x : affineActionScheme k Ω ⟶ affineActionScheme k E,
        x ≫ affineInvariantProjection k E H.X = y ∧
        IsClosed (affineGeometricOrbit k E H.X Ω x) ∧
        ∀ z : affineActionScheme k Ω ⟶ affineActionScheme k E,
          z ≫ affineInvariantProjection k E H.X = y →
          affineGeometricOrbit k E H.X Ω x ⊆ closure (affineGeometricOrbit k E H.X Ω z) ∧
          (IsClosed (affineGeometricOrbit k E H.X Ω z) →
            affineGeometricOrbit k E H.X Ω z = affineGeometricOrbit k E H.X Ω x)) ∧
    (∀ (K : Type u) [Field K] [Algebra k K],
      (∃ e : K ⊗[k] (affineInvariants k E H.X) ≃+* extendedAffineInvariants k E H.X K,
        ∀ (c : K) (a : affineInvariants k E H.X),
          (e (c ⊗ₜ[k] a) : Γ(((Over.pullback
              (ProjectiveMatrixCentralCover.extension k K)).obj (affineActionScheme k E)).left,
            ⊤)) =
          (pullback.snd (affineActionScheme k E).hom
            (ProjectiveMatrixCentralCover.extension k K)).appTop.hom
              ((Scheme.ΓSpecIso (.of K)).inv.hom c) *
          (pullback.fst (affineActionScheme k E).hom
            (ProjectiveMatrixCentralCover.extension k K)).appTop.hom
              ((Scheme.ΓSpecIso (.of E)).inv.hom a)) ∧
      (∃ e : ((Over.pullback (ProjectiveMatrixCentralCover.extension k K)).obj
          (affineInvariantSpectrum k E H.X)).left ≅
            Spec (.of (extendedAffineInvariants k E H.X K)),
        ((Over.pullback (ProjectiveMatrixCentralCover.extension k K)).map
          (affineInvariantProjection k E H.X)).left ≫ e.hom =
        ((Over.pullback (ProjectiveMatrixCentralCover.extension k K)).obj
          (affineActionScheme k E)).left.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (extendedAffineInvariants k E H.X K).subtype)) ∧
      ∀ D : Set (affineActionScheme k E).left, IsClosed D →
        (ModObj.smul (M := H.X) (X := affineActionScheme k E)).left ⁻¹' D =
          (snd H.X (affineActionScheme k E)).left ⁻¹' D →
        ((Over.pullback (ProjectiveMatrixCentralCover.extension k K)).map
            (affineInvariantProjection k E H.X)).left ''
          ((pullback.fst (affineActionScheme k E).hom
            (ProjectiveMatrixCentralCover.extension k K)) ⁻¹' D) =
          (pullback.fst (affineInvariantSpectrum k E H.X).hom
            (ProjectiveMatrixCentralCover.extension k K)) ⁻¹'
              ((affineInvariantProjection k E H.X).left '' D)) := by
  sorry

end AlgebraicGeometry.SchemeAction
