/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import WeilConjectures.AlgebraicGeometry.FlatFpLqfBoundedStratification
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-!
# Constant geometric degree makes a separated étale chart finite

Source: Stacks Project, Decent Spaces, Tag 07S8
(lemma-quasi-compact-reasonable-stratification), using More on Morphisms, Tag 07RY
(blueprint: lem-sfb-space-constant-degree-etale-finite).

Scheme tests and geometric fibres are represented by Yoneda pullback squares. Exactly
`d` points means existence of a bijection with `Fin d`, including the empty fibre at zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact separated representable étale map from a scheme to an algebraic
space, with constant geometric fibre cardinality `d`, is finite locally free of degree
`d` and étale on every scheme test. No Noetherian or finite-type condition is imposed
on the structure maps to the base scheme.

Source: Stacks Project, Decent Spaces, Tag 07S8, its degree-stratum universal property;
More on Morphisms, Tag 07RY (blueprint: lem-sfb-space-constant-degree-etale-finite).

Proof:
1. For a scheme test T → X, represent W ×_X T by Y with projection p : Y → T,
   using def-trf-algebraic-space and lem-trf-space-fibre-products-etale-covers.
   It is étale by def-weil-etale-morphism and quasi-compact by the test hypothesis.
   Its diagonal is a base change of the diagonal of f, hence a closed immersion by
   lem-weil-pbc-closed-immersion-base-change. Thus p is separated, flat, locally of
   finite presentation, and locally quasi-finite by
   lem-weil-pbc-unramified-quasi-finite-at-points.
2. Every ordinary fibre F over k = κ(t) is quasi-compact by
   lem-pc-quasi-compact-base-change and is a disjoint union of spectra of finite
   separable extensions by lem-weil-pbc-etale-fibre-discrete-separable-points.
   Compactness makes this union finite. Each component is finite by
   def-weil-finite-integral-morphism; lem-weil-pbc-finite-coproduct makes F finite.
   By lem-weil-pbc-finite-over-field-affine-finite-dim write F = Spec B with B a
   finite-dimensional k-algebra, and put e_t = dim_k B. The empty case has B = 0.
3. Extend k to an algebraic closure Ω. By lem-weil-pbc-fibre-degree-base-change,
   the geometric fibre has degree e_t. Associativity of fibre products identifies
   it with the geometric fibre of f, so it has exactly d points. The decomposition
   of lem-weil-pbc-etale-fibre-discrete-separable-points now has every residue field
   equal to Ω, since Ω is algebraically closed. Its section algebra is Ω^d, so
   e_t = d, also for d = 0.
4. The fibres of p are finite of degree d, giving a universal degree bound.
   Apply lem-weil-pbc-flat-fp-lqf-bounded-stratification to p. The universal property
   at each residue-field point puts every t in the degree-d stratum, since its
   fibre is finite, flat, locally of finite presentation and has degree d by
   def-pc-finite-locally-free. Apply the same property to the identity of T to
   conclude p is finite locally free of degree d. It remains étale by step 1.
   This works for every test T, including the empty test, with no reducedness or
   finite-type assumption on T or the maps to S. -/
theorem finiteLocallyFreeOfDegree_of_constant_geometric_cardinality
    {S : Scheme.{u}} (X : AlgebraicSpace S) (W : Over S)
    (f : yoneda.obj W ⟶ X.obj.obj) (hf : IsEtale f)
    (hqc : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) f)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal f))
    (d : ℕ)
    (hdegree : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (CommRingCat.of Ω) ⟶ S)
      (a : yoneda.obj (Over.mk b) ⟶ X.obj.obj)
      (U : Over S) (p : U ⟶ Over.mk b) (q : yoneda.obj U ⟶ yoneda.obj W),
      IsPullback q (yoneda.map p) f a → Nonempty (U.left ≃ Fin d)) :
    IsRepresentableWith
      (fun _ _ p ↦ p.left.IsFiniteLocallyFreeOfDegree d ∧ Etale p.left) f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
