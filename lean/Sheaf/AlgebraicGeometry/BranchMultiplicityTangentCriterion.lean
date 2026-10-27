/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullback

import WeilConjectures.RingTheory.CompletionLocalizedAlgebraFiniteQuotients
import Sheaf.RingTheory.HilbertSamuelGrowthDimension
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.CompleteLocalQuotient
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Sheaf.RingTheory.CompleteLocalCotangentSurjectivity

/-! # Branch multiplicities and tangent lines of an embedded reduced curve

Source: Morrison, arXiv:0810.2340, Section 3.2, Theorem 8(4)--(6), pp. 14--15;
Stacks Project, Tags 0B2E, 0B2F, 0C1R, 0C3V, 0C1U and 0CBW.
(blueprint: lem-sfb-branch-multiplicity-tangent-criterion).

A projective line is recorded by its space of vanishing homogeneous linear forms:
this is a codimension-two subspace of the space of linear forms. Its equations below
are defined by the actual ambient tangent vectors, independently of second-order vanishing
on the curve. All branch points include their component label, including self-intersections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace
open scoped BigOperators

namespace AlgebraicGeometry.ProjectiveCurveBranches

/-- The projective ambient space with `r` homogeneous coordinates.
Source: Morrison, Section 3.2 (blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
abbrev Ambient (k : Type u) [Field k] (r : ℕ) : Scheme.{u} :=
  ℙ(ULift.{u} (Fin r); Spec (.of k))

/-- One component of the canonical componentwise normalization.
Source: Stacks 0CDV (blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
abbrev Component (D : Scheme.{u}) (Z : irreducibleComponents D) : Scheme.{u} :=
  (D.reducedNormalizationComponent Z).normalization

/-- The actual normalization fibre, with its component labels retained.
Source: Morrison, Theorem 8(4)--(6)
(blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
def Branch (D : Scheme.{u}) (p : D) : Type u :=
  Σ Z : irreducibleComponents D, {q : Component D Z // D.normalizedComponentMap Z q = p}

/-- The local homomorphism from the curve point to its specified branch.
Source: Stacks 0C1R (blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
def localMap (D : Scheme.{u}) (p : D) (q : Branch D p) :
    D.presheaf.stalk p →+* (Component D q.1).presheaf.stalk q.2.1 :=
  ((D.presheaf.stalkCongr (.of_eq q.2.2.symm)).hom ≫
    (D.normalizedComponentMap q.1).stalkMap q.2.1).hom

/-- The ideal whose positive DVR exponent is the branch multiplicity.
Source: Morrison, Theorem 8(4)--(6)
(blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
def branchIdeal (D : Scheme.{u}) (p : D) (q : Branch D p) :
    Ideal ((Component D q.1).presheaf.stalk q.2.1) :=
  (IsLocalRing.maximalIdeal (D.presheaf.stalk p)).map (localMap D p q)

/-- The hyperplane degree on the canonical normalized component, with induced base map.
Source: Morrison, Theorem 8; Stacks 0AYR
(blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
def componentDegree (k : Type u) [Field k] (r : ℕ) (D : Scheme.{u})
    (i : D ⟶ Ambient k r) (Z : irreducibleComponents D) : ℤ :=
  @Scheme.Modules.degree k _ (Component D Z)
    ⟨(D.normalizedComponentMap Z ≫ i) ≫ (Ambient k r ↘ Spec (.of k))⟩
    ((Scheme.Modules.tensorPullback (D.normalizedComponentMap Z ≫ i)).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of k)) 1))

/-- The slope of the eventually linear local length function, retaining finite length.
The shift by one is exactly the convention in the statement.
Source: Stacks 00K8, 00KQ (blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
def HasMultiplicity (D : Scheme.{u}) (p : D) (t : ℕ) : Prop :=
  ∃ a : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Module.length (D.presheaf.stalk p)
      (D.presheaf.stalk p ⧸ IsLocalRing.maximalIdeal (D.presheaf.stalk p) ^ (n + 1)) < ⊤ ∧
    ((Module.length (D.presheaf.stalk p)
      (D.presheaf.stalk p ⧸ IsLocalRing.maximalIdeal (D.presheaf.stalk p) ^ (n + 1))).toNat :
        ℤ) = (t : ℤ) * (n : ℤ) + a

/-- The actual image of the recorded scheme tangent map in the common ambient tangent space.
The equality of image points transports only the point index. The residue-field isomorphism
is the canonical map, with bijectivity a proposition, not a chosen identification.
Source: Stacks 0B2F (blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
def tangentImage (k : Type u) [Field k] (r : ℕ) (D : Scheme.{u})
    (i : D ⟶ Ambient k r) (p : D) (q : Branch D p) :
    Set (schemeTangentSpace k (Ambient k r) (Ambient k r ↘ Spec (.of k)) (i p)) :=
  {θ | ∃ he : Function.Bijective
      ((D.normalizedComponentMap q.1 ≫ i).residueFieldMap q.2.1).hom,
    ∃ v : schemeTangentSpace k (Component D q.1)
        ((D.normalizedComponentMap q.1 ≫ i) ≫ (Ambient k r ↘ Spec (.of k))) q.2.1,
      θ = cast (congrArg
        (schemeTangentSpace k (Ambient k r) (Ambient k r ↘ Spec (.of k)))
        (congrArg i q.2.2))
        (schemeTangentMap k (Component D q.1) (Ambient k r)
          ((D.normalizedComponentMap q.1 ≫ i) ≫ (Ambient k r ↘ Spec (.of k)))
          (Ambient k r ↘ Spec (.of k)) (D.normalizedComponentMap q.1 ≫ i) rfl q.2.1 he v)}

/-- A homogeneous linear form, divided by a nonvanishing coordinate and taken as a germ.
Source: Morrison, Theorem 8(6) (blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
def linearGerm (k : Type u) [Field k] (r : ℕ) (x : Ambient k r)
    (j : ULift.{u} (Fin r))
    (hx : x ∈ ProjectiveSpace.standardOpen (ULift.{u} (Fin r)) (Spec (.of k)) j)
    (a : ULift.{u} (Fin r) → k) : (Ambient k r).presheaf.stalk x :=
  ∑ m : ULift.{u} (Fin r),
    (StructureSheaf.toStalk k ((Ambient k r ↘ Spec (.of k)) x) ≫
      (Ambient k r ↘ Spec (.of k)).stalkMap x) (a m) *
    (Ambient k r).presheaf.germ
      (ProjectiveSpace.standardOpen (ULift.{u} (Fin r)) (Spec (.of k)) j) x hx
      (ProjectiveSpace.coordRatio (ULift.{u} (Fin r)) (Spec (.of k)) j m)

/-- Equations of the projective line determined by a tangent direction. A form vanishes
at the point and on the tangent direction precisely when its whole dual-number pullback
is zero. Quantification over the closed-point equality makes the stalk transport explicit.
Source: Stacks 0B2E, 0B2F; Morrison, Theorem 8(6)
(blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
def lineEquations (k : Type u) [Field k] (r : ℕ) (D : Scheme.{u})
    (i : D ⟶ Ambient k r) (p : D) (q : Branch D p) : Set (ULift.{u} (Fin r) → k) :=
  {a | ∀ (j : ULift.{u} (Fin r))
      (hp : i p ∈ ProjectiveSpace.standardOpen (ULift.{u} (Fin r)) (Spec (.of k)) j)
      (θ : schemeTangentSpace k (Ambient k r) (Ambient k r ↘ Spec (.of k)) (i p)),
    θ ∈ tangentImage k r D i p q →
    ∀ hθ : θ.val (IsLocalRing.closedPoint (DualNumber ((Ambient k r).residueField (i p)))) =
        i p,
      (eqToHom (congrArg (fun x : Ambient k r ↦ (Ambient k r).presheaf.stalk x) hθ.symm) ≫
        Scheme.stalkClosedPointTo θ.val) (linearGerm k r (i p) j hp a) = 0}

/-- A form has order at least two on a branch in every projective coordinate frame.
This includes the zero germ, so an identically zero pullback has infinite order.
Source: Morrison, Theorem 8(6) (blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
def HasOrderAtLeastTwo (k : Type u) [Field k] (r : ℕ) (D : Scheme.{u})
    (i : D ⟶ Ambient k r) (p : D) (q : Branch D p)
    (a : ULift.{u} (Fin r) → k) : Prop :=
  ∀ (j : ULift.{u} (Fin r))
    (hp : i p ∈ ProjectiveSpace.standardOpen (ULift.{u} (Fin r)) (Spec (.of k)) j),
    localMap D p q ((i.stalkMap p) (linearGerm k r (i p) j hp a)) ∈
      IsLocalRing.maximalIdeal ((Component D q.1).presheaf.stalk q.2.1) ^ 2

/-- The split-node completion as a complete local k-algebra. A ring isomorphism preserves
maximal ideals and all their powers, hence is automatically a homeomorphism for the adic
complete-local topologies. The coefficient equation imposes the given structural k-action.
Source: Stacks 0C1U, 0CBW (blueprint: lem-sfb-branch-multiplicity-tangent-criterion). -/
def HasSplitNodeCompletion (k : Type u) [Field k] (r : ℕ) (D : Scheme.{u})
    (i : D ⟶ Ambient k r) (p : D) : Prop :=
  ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk p))
      (D.presheaf.stalk p) ≃+*
      (MvPowerSeries (Fin 2) k ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}),
    ∀ a : k,
      e (AdicCompletion.of (IsLocalRing.maximalIdeal (D.presheaf.stalk p))
        (D.presheaf.stalk p)
        ((StructureSheaf.toStalk k (((i ≫ (Ambient k r ↘ Spec (.of k)))) p) ≫
          (i ≫ (Ambient k r ↘ Spec (.of k))).stalkMap p) a)) =
        algebraMap k (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}) a

/-- Branch multiplicities, component degree bounds, and both double-point tangent cases.

Source: Morrison, Section 3.2, Theorem 8(4)--(6), printed pp. 14--15, expanded using
Stacks 0C1R, 0C3V, 0B2E, 0B2F, 0C1U, 0CBW and 06GZ.
(blueprint: lem-sfb-branch-multiplicity-tangent-criterion).

Proof plan:
1. Apply curve-delta completion data and normalized-branch coordinates. Projective affine
charts make D finite type. The normalization is finite, its fibre is nonempty and finite,
and the branch local rings are DVRs. Finite-quotient comparison gives nonzero proper
extended ideals, uniquely maximal-ideal powers with positive exponents b_q.
2. Finite-quotient comparison decomposes B/m^N B into branch quotients. Their uniformizer
filtrations have N b_q residue-field factors. Length additivity gives N times sum b_q.
3. Finite colength delta gives m^c B contained in A for c=max(1,delta). The two quotient
surjections give delta+h(N-c) <= N sum b_q <= delta+h(N). Hilbert-Samuel growth is linear;
dividing by N identifies its slope with sum b_q.
4. A hyperplane through p not containing a chosen component pulls back to a nonzero
section vanishing to order b_q at every branch above p. The smooth-curve section-degree
cap gives the component bound. For an empty component fibre use any nonzero coordinate.
5. Ambient affine coordinates generate m_p. Their branch cotangent map vanishes exactly
when the extended ideal is contained in m_q^2, equivalently b_q>=2. Rational tangent/cotangent
duality gives the same criterion for the tangent map. Otherwise its image is one-dimensional.
6. At multiplicity two with all maps nonzero, positivity and the sum give exactly two
branches of exponent one. Their nonzero tangent images give codimension-two spaces of
linear equations, the two projective lines through p.
7. Equal-constant branch power series give H contained in P=k[[u,v]]/(uv). Distinct tangent
lines give surjectivity on cotangents; complete-local cotangent surjectivity yields H=P.
8. Conversely split-node component normalization gives the two coordinate branch maps.
Completion modulo powers identifies cotangents, and ambient coordinates surject onto them;
the two tangent directions, hence the two projective lines, are distinct. This includes
two branches on the same component.
9. If the lines agree, every form vanishing on their common line has zero constant and
first tangent coefficient on both branches, hence belongs to each squared maximal ideal.
All arguments hold in every characteristic and include an identically zero pulled-back form. -/
theorem branch_multiplicity_tangent_criterion
    (k : Type u) [Field k] [IsAlgClosed k] (r : ℕ) (hr : 2 ≤ r)
    (D : Scheme.{u}) [IsReduced D] (i : D ⟶ Ambient k r) [IsClosedImmersion i]
    (hpure : D.IsPureDimension 1) (p : D) (hp : IsClosed ({p} : Set D))
    (hprational : Function.Bijective
      ((StructureSheaf.toStalk k ((i ≫ (Ambient k r ↘ Spec (.of k))) p) ≫
        (i ≫ (Ambient k r ↘ Spec (.of k))).stalkMap p ≫ D.residue p).hom))
    (hnormal : ∀ Z : irreducibleComponents D,
      Smooth ((D.normalizedComponentMap Z ≫ i) ≫ (Ambient k r ↘ Spec (.of k))) ∧
      IsProper ((D.normalizedComponentMap Z ≫ i) ≫ (Ambient k r ↘ Spec (.of k))) ∧
      ConnectedSpace (Component D Z))
    (t : ℕ) (ht : HasMultiplicity D p t) :
    ∃ (b : Branch D p → ℕ) (s : Finset (Branch D p)),
      (∀ q : Branch D p, q ∈ s) ∧
      (∀ q : Branch D p, 1 ≤ b q ∧
        branchIdeal D p q =
          IsLocalRing.maximalIdeal ((Component D q.1).presheaf.stalk q.2.1) ^ b q) ∧
      t = ∑ q ∈ s, b q ∧
      (∀ Z : irreducibleComponents D,
        (∑ q ∈ s, @ite ℤ (q.1 = Z) (Classical.propDecidable _) (b q : ℤ) 0) ≤
          componentDegree k r D i Z) ∧
      (∀ q : Branch D p, tangentImage k r D i p q = {0} ↔ 2 ≤ b q) ∧
      (t = 2 → (∀ q : Branch D p, tangentImage k r D i p q ≠ {0}) →
        ∃ q₁ q₂ : Branch D p, q₁ ≠ q₂ ∧
          (∀ q : Branch D p, q = q₁ ∨ q = q₂) ∧ b q₁ = 1 ∧ b q₂ = 1 ∧
          (∀ q : Branch D p,
            Module.finrank ((Ambient k r).residueField (i p))
              (Submodule.span ((Ambient k r).residueField (i p))
                (tangentImage k r D i p q)) = 1 ∧
            ∃ W : Submodule k (ULift.{u} (Fin r) → k),
              (W : Set (ULift.{u} (Fin r) → k)) = lineEquations k r D i p q ∧
              Module.finrank k ((ULift.{u} (Fin r) → k) ⧸ W) = 2) ∧
          (lineEquations k r D i p q₁ ≠ lineEquations k r D i p q₂ ↔
            HasSplitNodeCompletion k r D i p) ∧
          (lineEquations k r D i p q₁ = lineEquations k r D i p q₂ →
            ∀ a : ULift.{u} (Fin r) → k, a ∈ lineEquations k r D i p q₁ →
              HasOrderAtLeastTwo k r D i p q₁ a ∧ HasOrderAtLeastTwo k r D i p q₂ a)) := by
  sorry

end AlgebraicGeometry.ProjectiveCurveBranches
