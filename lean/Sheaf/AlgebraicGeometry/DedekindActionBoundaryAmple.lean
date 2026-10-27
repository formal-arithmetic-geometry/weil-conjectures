/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Ampleness of an orbit-meeting Cartier boundary over a Dedekind base

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §6.4, Proposition 2,
printed pp.153--154 (PDF pp.159--160); absolute ampleness over an affine base
is Stacks Project, Tag 01VK.
(blueprint: lem-sfb-dedekind-action-boundary-ampleness)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- An effective Cartier divisor with affine complement meeting every orbit has an
absolutely ample associated line bundle over the affine Dedekind base.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §6.4, Proposition 2,
printed pp.153--154; Stacks Project, Tag 01VK.
(blueprint: lem-sfb-dedekind-action-boundary-ampleness)

Proof plan:
1. Put L = J.toModulesᵛ. The canonical section of
   lem-sc-canonical-section-zero-scheme has zero scheme J.subscheme, so its
   nonvanishing locus is J.support.compl. On a chart with J = (f), its value is f.
2. Apply lem-sfb-dedekind-invariant-component-ample-test: it suffices to test the
   pullback to every invariant clopen connected component Y over a strictly henselian
   trait or separably closed field T, with Y surjective over T and nonempty
   geometrically connected generic fibre. No connectedness of X is needed.
3. By lem-weil-pbc-invertible-pullback-tensor the restricted section has nonvanishing
   open Y ∩ A_T. The scheme A_T is affine, and its clopen subset Y ∩ A_T is affine
   (the functions 1 and 0 glue to an idempotent cutting it out). By
   lem-weil-pbc-surjective-base-change, the orbit map remains surjective over T.
   Invariance of Y and translation by the inverse identify its inverse image with
   H_T ×_T (Y ∩ A_T), proving orbit coverage on Y.
4. Smoothness and separated finite type persist under base change and clopen
   restriction (lem-pc-proper-base-change, lem-pod-separated-finite-type-base-change).
   Geometric connectedness of the group fibres persists too. Apply
   lem-sfb-dedekind-action-square-power to obtain a positive power M of L|Y satisfying
   the square condition. Finite type over the Noetherian test base gives local finite
   presentation by pqf-lem-lft-fp-locnoeth; separatedness gives quasi-separatedness.
   The positive power of the canonical section has the same affine nonvanishing open.
   Its group translates cover Y, so lem-sfb-square-action-affine-orbit-criterion gives
   ampleness of M.
5. Every affine section locus for a positive power of M is also one for a positive
   power of L|Y, proving ampleness of L|Y. The invariant-component test now proves
   ampleness of L. Over the affine base, relative ampleness is absolute (01VK).
   For empty X both quasi-compactness and the section-neighbourhood condition hold.

The point z in the orbit hypothesis is a point of the actual scheme fibre product,
not a pair of points of its factors. Its second projection lies in the complement;
thus this is exactly surjectivity of the action restricted to H ×_S A. -/
theorem isAmple_dual_cartierIdeal_of_affine_orbit_complement
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]
    (hdim : ringKrullDim D = 1)
    (H X : Over (Spec (CommRingCat.of D))) [GrpObj H] [ModObj H X]
    [Smooth H.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom]
    [QuasiCompact H.hom] [GeometricallyConnected H.hom]
    [Smooth X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom]
    (J : X.left.IdealSheafData) (hJ : J.IsInvertible)
    (haffine : IsAffineOpen J.support.compl)
    (horbits : ∀ x : X.left, ∃ z : (H ⊗ X).left,
      (snd H X).left z ∈ J.support.compl ∧ (γ[H, X]).left z = x) :
    @IsAmple X.left J.toModulesᵛ hJ.isInvertible_dual_toModules := by
  sorry

end AlgebraicGeometry.Scheme.Modules
