/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.Curve.CompleteDivisorLinearSystem
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import Sheaf.AlgebraicGeometry.DivisorClassCurve
import Sheaf.AlgebraicGeometry.DivisorModuleLocal
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import Sheaf.AlgebraicGeometry.ProperCurveBundlePullbackDegree
import Sheaf.AlgebraicGeometry.Curve.ProperFunctionFieldMorphisms
import Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
import Sheaf.AlgebraicGeometry.RationalSectionDivisor
import Sheaf.AlgebraicGeometry.ProperFiniteFibreFiniteNeighbourhood
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Uniqueness of a degree-two pencil

Source: Milne, Jacobian Varieties, III proof of Theorem 12.1(b), printed p.120;
Stacks Project, Curves, Tags 0CCP, 0CCR and 0CCT.
(blueprint: lem-sfb-degree-two-pencil-uniqueness)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Nonconstant degree-two maps use the actual induced map of generic stalks.
Degree means total field degree, with no separability condition.
Source: Milne III 12.1(b), p.120; Stacks Curves 0CCR.
(blueprint: lem-sfb-degree-two-pencil-uniqueness) -/
noncomputable def Hom.IsDegreeTwoCurveMap
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (π : C ⟶ ProjectiveLine (Spec (.of k))) : Prop :=
  letI := (C.smooth_connected_curve_local_rings k f).choose
  (¬ ∃ y : Spec (.of k) ⟶ ProjectiveLine (Spec (.of k)),
    y ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ ∧ f ≫ y = π) ∧
  ∃ hη : π (genericPoint C) = genericPoint (ProjectiveLine (Spec (.of k))),
    @Module.finrank (ProjectiveLine (Spec (.of k))).functionField C.functionField _ _
      (π.functionFieldMap hη).hom.toAlgebra.toModule = 2

/-- The fibre divisor is the canonical divisor pullback of a closed point, including
ramification multiplicities. Finiteness is a conclusion in the main statement.
Source: Milne III 12.1(b), p.120; Stacks Curves 0CCR, fibre divisors.
(blueprint: lem-sfb-degree-two-pencil-uniqueness) -/
noncomputable def Hom.degreeTwoFiberDivisor
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (π : C ⟶ ProjectiveLine (Spec (.of k))) (hπ : IsFinite π)
    (Q : closedPoints (ProjectiveLine (Spec (.of k)))) : C.Divisor :=
  letI := (C.smooth_connected_curve_local_rings k f).choose
  letI := isNoetherian_of_locallyOfFiniteType f
  letI := hπ
  Divisor.pullback π (Finsupp.single Q 1)

/-- On a smooth projective connected curve of genus at least two, a moving complete
system of degree two is a unique basepoint-free pencil. It has one member through each
point, is realized by a finite degree-two map, and all such maps differ by a base-field
projective-line automorphism. The introductory section/divisor dictionary is included.

Source: Milne III proof of Theorem 12.1(b), p.120; Stacks Curves 0CCP, 0CCR, 0CCT.
(blueprint: lem-sfb-degree-two-pencil-uniqueness)

Proof plan (the nine steps of the node):
1. Projectivity implies properness (lem-kun-projective-implies-proper); smooth connected
   curves are integral and Noetherian (lem-sc-smooth-connected-curve-local-rings).
   The divisor-class dictionary (lem-sc-divisor-class-curve) makes O(D) invertible.
   Riemann--Roch (lem-sc-riemann-roch) identifies divisor degree with Euler degree,
   and proper coherent finiteness (lem-pc-coherent-hi) gives finite section spaces.
2. The valuation bounds in def-sc-divisor identify a nonzero section s with D + div(s).
   All members arise this way. Equal divisors imply their ratio and its inverse are
   regular everywhere, hence nonzero scalars by lem-sc-global-functions. This gives
   the projectivization dictionary and the stated scheme of members.
3. Distinct members give two independent sections. Apply
   lem-sfb-linear-series-degree-dimension-bound with degree two and genus at least two:
   the section dimension is at most two. A base point would give two independent
   sections in degree one, contradicting the same bound. Closed points are rational
   by lem-weil-pbc-closed-point-residue-field-base, and the local divisor generators
   (lem-sc-divisor-module-local) show that evaluation generates the bundle everywhere.
4. Evaluation at Q has a one-dimensional kernel in this two-dimensional section space.
   Its unique line gives the unique member containing Q, including a double point 2Q.
5. For two pencils L,M, four independent products of basis sections would contradict
   the degree-four bound (lem-sfb-linear-series-degree-dimension-bound). Group a nonzero
   relation as s₀a + s₁b = 0 with (a,b) nonzero; degrees add by def-sc-pic0.
6. On the opens where s₁ and s₀ generate, a/s₁ and -b/s₀ glue to a nonzero section of
   M tensor L-inverse, of degree zero. By lem-trf-curve-section-degree-positivity it
   vanishes nowhere, hence trivializes that bundle. The divisor-class dictionary
   identifies the two complete systems.
7. A generating basis defines the projective-line map by
   lem-weil-pbc-projective-space-functor-of-points and
   def-weil-pbc-morphism-to-projective-space-by-sections. It is nonconstant by independence.
   Apply lem-asd-projective-line-genus-zero, lem-sfb-proper-curve-function-field-morphisms,
   and lem-sfb-proper-curve-bundle-pullback-degree to see its total degree is two.
   Locally its fibres are zeros of the linear combinations v s₀ - u s₁, with multiplicity.
8. Properness follows from lem-weil-pbc-proper-to-separated. Its finite fibres give finite
   neighbourhoods by thm-sc-proper-finite-fibre-finite-neighbourhood, covering the target.
9. Conversely, a nonconstant degree-two map pulls back O(1) to a degree-two bundle by
   lem-sfb-proper-curve-bundle-pullback-degree. Its two generating coordinate sections
   are independent. Their effective rational-section divisors (def-sc-rational-section-divisor,
   lem-sc-line-bundle-rational-section) give the unique complete system. Two such maps
   are two bases of the same section space; the invertible basis-change matrix gives
   an automorphism of the projective line, whose inverse comes from the inverse matrix.
-/
theorem degree_two_pencil_uniqueness
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsHProjective f]
    (hg : 2 ≤ f.genus) :
    (∀ D : C.Divisor, (∀ P, 0 ≤ D P) →
      ∃ e : Projectivization k (Divisor.linearSystemSections k C f D) ≃
          ↥(Divisor.completeLinearSystem k C f D),
        ∀ (s : Divisor.linearSystemSections k C f D) (hs : s ≠ 0),
          Divisor.sectionRepresentsDivisor k C f D s (e (Projectivization.mk k s hs)).val) ∧
    (∀ D : C.Divisor, (∀ P, 0 ≤ D P) → Divisor.degree C D = 2 →
      (∃ E₁ ∈ Divisor.completeLinearSystem k C f D,
        ∃ E₂ ∈ Divisor.completeLinearSystem k C f D, E₁ ≠ E₂) →
      Module.finrank k (Divisor.linearSystemSections k C f D) = 2 ∧
      Nonempty (Divisor.linearSystemScheme k C f D ≅ ProjectiveLine (Spec (.of k))) ∧
      (∀ Q : closedPoints C,
        ∃ E ∈ Divisor.completeLinearSystem k C f D, E Q = 0) ∧
      (∀ E : C.Divisor, (∀ P, 0 ≤ E P) → Divisor.degree C E = 2 →
        (∃ E₁ ∈ Divisor.completeLinearSystem k C f E,
          ∃ E₂ ∈ Divisor.completeLinearSystem k C f E, E₁ ≠ E₂) →
        Divisor.completeLinearSystem k C f E = Divisor.completeLinearSystem k C f D) ∧
      (∀ Q : closedPoints C, ∃! E : C.Divisor,
        E ∈ Divisor.completeLinearSystem k C f D ∧ 0 < E Q) ∧
      (∃ (π : C ⟶ ProjectiveLine (Spec (.of k))) (hπ : IsFinite π),
        π ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = f ∧
        Hom.IsDegreeTwoCurveMap k C f π ∧
        Set.range (Hom.degreeTwoFiberDivisor k C f π hπ) =
          Divisor.completeLinearSystem k C f D)) ∧
    (∀ π : C ⟶ ProjectiveLine (Spec (.of k)),
      π ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = f →
      Hom.IsDegreeTwoCurveMap k C f π →
      ∃ (hπ : IsFinite π) (D : C.Divisor),
        (∀ P, 0 ≤ D P) ∧ Divisor.degree C D = 2 ∧
        (∃ E₁ ∈ Divisor.completeLinearSystem k C f D,
          ∃ E₂ ∈ Divisor.completeLinearSystem k C f D, E₁ ≠ E₂) ∧
        Set.range (Hom.degreeTwoFiberDivisor k C f π hπ) =
          Divisor.completeLinearSystem k C f D) ∧
    (∀ π₁ π₂ : C ⟶ ProjectiveLine (Spec (.of k)),
      π₁ ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = f →
      π₂ ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = f →
      Hom.IsDegreeTwoCurveMap k C f π₁ → Hom.IsDegreeTwoCurveMap k C f π₂ →
      ∃ a : Aut (ProjectiveLine (Spec (.of k))),
        a.hom ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) =
          ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) ∧ π₁ ≫ a.hom = π₂) := by
  sorry

end AlgebraicGeometry.Scheme
