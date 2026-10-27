/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity
import Sheaf.AlgebraicGeometry.DegreeWeightedIrreducibleComponents
import Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction
import Sheaf.AlgebraicGeometry.ProperCurveBundlePullbackDegree
import Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange

/-! # Extremal subcurve degree of a generically trivial nodal-trait line

Source: Morrison, arXiv:0810.2340, Section 3.3, proof of Proposition 10, printed p. 16;
Stacks Project, Perfect Complexes, Tags 0B9T and 0BDN; Varieties, Tags 0AYW, 0AYZ,
0B40 and 0AYY; Curves, Tag 0C4D
(blueprint: lem-sfb-nodal-trait-twister-extremal-degree).

A cartesian square specifies any model of the geometric closed fibre. A finite subset
of its irreducible components specifies the unique reduced component union. Its degree
is the sum on canonical normalizations, and its boundary is its intersection with the
union of all remaining components. No total-space regularity is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A generically trivial invertible module on a projective flat nodal trait is trivial
on the geometric closed fibre, or has degree at least the positive boundary-node count
on a nonempty proper reduced component union. The union need not be connected. Self-nodes
inside either side do not count as boundary nodes. The statement allows persistent generic
nodes, arbitrary smoothing thickness and singular total spaces; components need not be Cartier.

Source: Morrison, Section 3.3, proof of Proposition 10, p. 16, boundary-zero argument;
the general-total-space extension follows the section-specialization proof below, using
Stacks Tags 0B9T, 0BDN, 02KH, 0AYW, 0AYZ, 0B40, 0AYY and 0C4D
(blueprint: lem-sfb-nodal-trait-twister-extremal-degree).

Proof, following the six DAG steps:
1. Projective-proper and projective-base-change give proper fibres. Both T and O_X are
   finitely presented and flat over R. Proper-flat-sheaf-euler-local-constancy (0B9T)
   identifies their generic and closed Euler characteristics, and its base-change clause
   gives the same equality over Omega. Generic triviality therefore gives total degree zero.
2. The nonempty generic fibre has a nonzero section of T. Semicontinuity-base-change
   (0BDN), in degree zero, specializes h0 >= 1 to the closed point. Flat-base-change-cohom
   (02KH) for the residue-field extension gives a nonzero section sigma on C.
3. Degree-weighted-irreducible-components (0AYW) gives finitely many proper integral
   components, with multiplicity one since C is reduced. Nodal-normalization-adjunction
   gives smooth proper connected normalizations and the two branches at each node.
   Proper-curve-bundle-pullback-degree (0AYZ), with function-field degree one, identifies
   the component and normalized degrees; their sum is zero. The components on which
   sigma is nonzero form a nonempty subset I, since a section vanishing at all generic
   points of a reduced scheme is zero.
4. If I is the whole component set, curve-section-degree-positivity (0B40) makes all
   component degrees nonnegative, and strictly positive if sigma has a zero. Their sum
   is zero, so sigma is nowhere zero on all normalizations, hence on C. It trivializes T|C.
5. Otherwise let Y be the reduced union indexed by I, and W its reduced complement.
   Both are nonempty. Connectedness gives a nonempty intersection B. It consists of
   nodes, each with exactly one branch on Y. On each component of Y let B_i be its
   normalized branch preimages over B. Then sum |B_i| = |B|. Since sigma is zero on W,
   its normalized component sections vanish at all these points.
6. Smooth-connected-curve-local-rings makes each reduced point divisor Cartier. The
   B_i are Omega-rational, so D_i = sum [q] has degree |B_i| by degree-base-change's
   rational-point formula (0AYY). The nonzero section factors through L_i(-D_i), which
   has nonnegative degree by curve-section-degree-positivity. The effective-divisor
   tensor formula gives degree L_i >= |B_i|, also for empty B_i. Sum over I to obtain
   degree_Y(T|C) >= |B| > 0. No vertical Cartier component is used.
-/
theorem nodal_trait_twister_extremal_degree
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProjective f] [Flat f] [LocallyOfFinitePresentation f]
    (hnodal : HasNodalGeometricFibres f)
    (hgeometric : ∀ (F : Type u) [Field F] [IsAlgClosed F]
      (t : Spec (.of F) ⟶ Spec (.of R)),
      IsReduced (pullback f t) ∧ (pullback f t).IsPureDimension 1)
    (T : X.Modules) [T.IsInvertible]
    (hgeneric : Nonempty
      ((Scheme.Modules.tensorPullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj T ≅
        SheafOfModules.unit
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).ringCatSheaf))
    (Ω : Type u) [Field Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
    [IsAlgClosure (IsLocalRing.ResidueField R) Ω]
    (C : Scheme.{u}) (i : C ⟶ X) (p : C ⟶ Spec (.of Ω))
    (hC : IsPullback i p f
      (Spec.map (CommRingCat.ofHom
        ((algebraMap (IsLocalRing.ResidueField R) Ω).comp (IsLocalRing.residue R))))) :
    Nonempty ((Scheme.Modules.tensorPullback i).obj T ≅ SheafOfModules.unit C.ringCatSheaf) ∨
      ∃ S : Finset (irreducibleComponents C),
        S.Nonempty ∧ (⋃ Z ∈ S, Z.1) ≠ (Set.univ : Set C) ∧
        (((⋃ Z ∈ S, Z.1) ∩
          ⋃ Z : irreducibleComponents C, ⋃ (_ : Z ∉ S), Z.1).ncard : ℤ) ≤
          ∑ Z ∈ S, markedNodalComponentDegree Ω (C.reducedNormalizationComponent Z)
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι
            ((Scheme.IdealSheafData.vanishingIdeal
              ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫ p)
            ((Scheme.Modules.tensorPullback i).obj T) ∧
        0 < ((⋃ Z ∈ S, Z.1) ∩
          ⋃ Z : irreducibleComponents C, ⋃ (_ : Z ∉ S), Z.1).ncard := by
  sorry

end AlgebraicGeometry
