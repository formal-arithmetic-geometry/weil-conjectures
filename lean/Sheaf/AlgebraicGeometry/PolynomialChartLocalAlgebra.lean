/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Local algebra comparison for a polynomial chart

Source: Stacks Project, Tags 00RE and 00R7, in the proof of Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-local-algebra)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The geometric part of the polynomial-chart criterion, without a depth assertion.

Source: Stacks Project, Tags 00RE (the dimension comparison in its proof), 00R7,
00RH, and 00P1 (the finite-type field dimension formula).
Proof: Write A = Gamma(T), B = Gamma(U), P = A[t_1,...,t_n]. The chart supplies
an A-algebra map P to B. Let p in Spec(A) lie below x, k = kappa(p), and q be
its prime in B tensor_A k. Put C = k[t_1,...,t_n], let q' be the contraction
of q to C, and take R = C localized at q'. Identify (B tensor_A k)_q with
S, the displayed fibre stalk of f, using Spec tensor-product and stalk-localization
isomorphisms and the open immersion U into X. Transport the localized chart map
along that ring isomorphism to obtain phi : R -> S. Polynomial regularity makes
R regular local, and finite type over k makes S Noetherian local. Quasi-finiteness
survives base change and localization; its closed fibre is a nonzero Artinian
local ring, so it has dimension zero. The quasi-finite local dimension inequality
gives dim(S) <= dim(R). Both dimensions are finite; call them r and d.
The residue extension kappa(q)/kappa(q') is finite, so both residue fields have
the same finite transcendence degree t over k. The field dimension formula gives
local fibre dimension r+t and polynomial dimension d+t = n. Open immersion of
fibres preserves dimension at the point, giving the displayed topological formula.
Finally, flatness of the original stalk map implies flatness of phi by base change
and localization. Conversely, localize A at p. The polynomial and B stalks are
essentially finitely presented A_p-algebras. B_x is a nonzero finite presentation
module over itself and is A_p-flat by flatness of f. Flatness of phi is precisely
flatness of its closed-fibre module over the polynomial closed fibre. Tag 00R7
therefore makes B_x flat over the polynomial stalk; the same stalk isomorphisms
identify this with flatness of e.stalkMap x. No Cohen-Macaulay or depth assertion
is used in this comparison.
(blueprint: lem-sbc-polynomial-chart-local-algebra) -/
theorem polynomial_chart_local_algebra
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e] [LocallyQuasiFinite e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    let S := (f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x))
    ∃ (R : CommRingCat.{u}) (_ : IsRegularLocalRing R)
      (φ : R →+* S) (_ : IsLocalHom φ) (d r t : ℕ),
      IsNoetherianRing S ∧
      ringKrullDim R = (d : WithBot ℕ∞) ∧
      ringKrullDim S = (r : WithBot ℕ∞) ∧
      ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map φ) = 0 ∧
      r ≤ d ∧
      topologicalKrullDimAt (f.asFiber (U.ι x)) = ((r + t : ℕ) : WithBot ℕ∞) ∧
      n = d + t ∧
      ((e.stalkMap x).hom.Flat ↔ φ.Flat) := by sorry

end AlgebraicGeometry
