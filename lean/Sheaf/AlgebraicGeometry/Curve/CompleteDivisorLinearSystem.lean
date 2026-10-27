/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Complete divisor linear systems

Source: Stacks Project, Curves, Tag 0CCT, remark-classical-linear-series;
Milne, Jacobian Varieties, III proof of Theorem 12.1(b), printed p.120.
(blueprint: def-sfb-complete-divisor-linear-system)

The scheme of members uses coordinates in a chosen actual vector-space basis.
Its coordinate vectors are sections, rather than linear functionals on sections.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Divisor

/-- The complete system consists of effective divisors whose difference from D is principal.
Source: Stacks 0CCT; Milne III 12.1(b), p.120.
(blueprint: def-sfb-complete-divisor-linear-system) -/
noncomputable def completeLinearSystem (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (D : C.Divisor) : Set C.Divisor :=
  letI := (C.smooth_connected_curve_local_rings k f).choose
  letI := isNoetherian_of_locallyOfFiniteType f
  {E | (∀ P, 0 ≤ E P) ∧ E - D ∈ C.principalDivisors}

/-- Global sections of the recorded divisor module, with scalars pulled back along f.
Source: Stacks 0CCT, the section space of a complete linear system.
(blueprint: def-sfb-complete-divisor-linear-system) -/
noncomputable def linearSystemSections (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (D : C.Divisor) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)).obj
    (ModuleCat.of Γ(C, ⊤) Γ(D.moduleOfSmoothConnectedCurve k C f, ⊤))

/-- The scheme of members: projective space in coordinates of a basis of H⁰(O(D)).
A different basis gives the canonically isomorphic projective space by change of coordinates.
Source: Stacks 0CCT, nonzero sections modulo scalars; Milne III 12.1(b), p.120.
(blueprint: def-sfb-complete-divisor-linear-system) -/
noncomputable def linearSystemScheme (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    [IsHProjective f] (D : C.Divisor) : Scheme.{u} :=
  ProjectiveSpace (Module.Free.ChooseBasisIndex k (linearSystemSections k C f D))
    (Spec (.of k))

/-- The coefficient formula E = D + div(s) for a section in the explicit divisor module.
The section is a locally constant function on the top open, so its value at P is its
rational-function representative. Nonzero sections are imposed by callers.
Source: Stacks 0CCT and the valuation definition of O(D) in def-sc-divisor.
(blueprint: def-sfb-complete-divisor-linear-system) -/
noncomputable def sectionRepresentsDivisor (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (D : C.Divisor) (s : linearSystemSections k C f D) (E : C.Divisor) : Prop :=
  letI := (C.smooth_connected_curve_local_rings k f).choose
  letI := isNoetherian_of_locallyOfFiniteType f
  ∀ P : closedPoints C, E P = D P + C.ord (s.val ⟨P.val, trivial⟩) P.val

end AlgebraicGeometry.Scheme.Divisor
