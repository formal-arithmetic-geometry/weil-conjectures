/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.TraceFormula.StrictSemistableCurve
public import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.RingTheory.BinomialLaurentNormalForm
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Flat

/-! # Flatness and finite presentation of the nodal polynomial model

Source: Stacks Project, curves.tex, Tag 0CBY, universal model preceding
`lemma-etale-local-structure-nodal-family`; morphisms.tex, Tags 01U5 and 01TP
(blueprint: lem-trf-nodal-polynomial-free-flat).

The affine model uses the existing `strictNodalRing` and its coefficient projection.
The model over a scheme is the existing base change of the universal nodal model;
on an affine open it is exactly the quotient by `uv-h`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The coefficient projection `Spec(A[u,v]/(uv-a)) → Spec A` is flat and locally
of finite presentation over every commutative ring, for every parameter.
Source: Stacks Project, curves.tex, universal model preceding Tag 0CBY;
morphisms.tex, Tags 01U5 and 01TP
(blueprint: lem-trf-nodal-polynomial-free-flat).

Proof:
1. Apply `strictNodalRing_basis_exists` from lem-sfb-binomial-laurent-normal-form.
   Its basis consists of 1 and the positive powers of u and v over any A, even
   when a is zero or a zero divisor. By lem-weil-pbc-projective-module-flat
   (`Module.Flat.of_free`), the quotient is A-flat. The coefficient ring map
   is flat by def-weil-pbc-flat-ring-map (`RingHom.flat_algebraMap_iff`).
2. By lem-weil-pbc-flat-ring-map-iff-flat-affine (`Flat.SpecMap_iff`), its
   spectrum morphism, which is the displayed standard coefficient projection,
   is flat.
3. The quotient has two generators and one relation uv-a. Taking the whole
   affine source and target supplies the finite-presentation witnesses at each
   point in def-sbc-locally-finite-presentation. No Noetherian, reducedness or
   nonzerodivisor hypothesis enters these steps. -/
theorem nodalPolynomial_flat_locallyOfFinitePresentation (A : CommRingCat.{u}) (a : A) :
    Flat (StrictSemistableModel.baseMap (StrictSemistableModel.nodal a)) ∧
      LocallyOfFinitePresentation
        (StrictSemistableModel.baseMap (StrictSemistableModel.nodal a)) := by
  sorry

/-- The nodal polynomial model glued over any scheme along a global function
has flat, locally finitely presented projection to that scheme.
Source: Stacks Project, curves.tex, universal model preceding Tag 0CBY;
morphisms.tex, Tags 01U3 and 01TP
(blueprint: lem-trf-nodal-polynomial-free-flat).

Proof:
4. The base change of the universal model along `nodalBaseMap h` restricts over
   each affine open Spec A of V to Spec(A[u,v]/(uv-h|Spec A)); its transition
   maps are coefficient restriction and fix u and v. Thus it is the glued W
   in the statement. At any point of W choose such an affine open around its
   image. Steps 1--3 above give flatness and local finite presentation on the
   resulting chart. Restricting to open neighbourhoods does not change stalks,
   so the map on local rings at the chosen point is flat. By
   def-weil-flat-morphism this proves flatness globally. The same affine charts
   with two generators and one relation are the witnesses for
   def-sbc-locally-finite-presentation at every point. No affineness of arbitrary
   intersections of affine opens, or extra condition on V or h, is needed. -/
theorem nodalModelProjection_flat_locallyOfFinitePresentation
    (V : Scheme.{u}) (h : Γ(V, ⊤)) :
    Flat (pullback.snd (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)) ∧
      LocallyOfFinitePresentation
        (pullback.snd (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)) := by
  sorry

end AlgebraicGeometry
