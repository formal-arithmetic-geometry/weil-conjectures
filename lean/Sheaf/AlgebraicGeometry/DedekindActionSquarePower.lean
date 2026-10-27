/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.RingTheory.RegularLocalDimOneIffNormal
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.FieldProductSquarePower
import Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization

/-! # A positive line power satisfies the square condition for a smooth action

Source: Bosch--Luetkebohmert--Raynaud, Neron Models, 6.3 Theorem 1 and Lemma 2,
printed pp.148--151, affine integral dimension-at-most-one specialization.
(blueprint: lem-sfb-dedekind-action-square-power)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A positive tensor power of every line on a smooth separated finite-type scheme with
nonempty geometrically connected generic fibre satisfies the square condition for a smooth
separated finite-type group action with geometrically connected fibres over a Noetherian
integrally closed domain of dimension at most one. Fields are included.

Products in `Over (Spec D)` are fibre products over `Spec D`. The map
`(snd X B ≫ g) • fst X B` sends `(x,b)` to `g(b)x`, so its tensor pullback is canonically
`tau_g^* M_B`. The generic geometric connectedness condition includes nonemptiness, because
`ConnectedSpace` includes `Nonempty`. The line `N` and the isomorphism are existential;
there are no chosen isomorphisms or coherence data, and `B` is arbitrary.

Source: Bosch--Luetkebohmert--Raynaud, Neron Models, 6.3 Theorem 1 and Lemma 2,
printed pp.148--151 (blueprint: lem-sfb-dedekind-action-square-power).

Proof:
1. The base is regular: its local rings are normal Noetherian domains of dimension at most
   one, hence fields or regular by `lem-weil-pbc-regular-local-dim-one-iff-normal`.
   Base change (`lem-pc-proper-base-change`), `lem-trf-smooth-composition`, and
   `lem-weil-pbc-regular-ring-smooth-ascent` make H, X, T = H times H, and Y = T times X
   regular. Finite type and `pqf-lem-locnoeth-lft` make them Noetherian. Smoothness and
   separated finite type imply finite presentation (`def-sbc-locally-finite-presentation`).
2. The geometric fibres of H and the generic fibre of X are integral by
   `lem-trf-smooth-connected-fibre-normal-integrality`. The product of two H-fibres is
   integral by `lem-sbc-smooth-connected-generic-geometry-core`. Normal components of X
   are disjoint open and closed (`rem-pc-regular-normal`). Smoothness implies flatness
   (`lem-pc-smooth-flat`), and `lem-trf-flat-module-torsionfree-domain` shows every nonempty
   affine open meets the generic fibre. Thus X is normal integral with dense generic fibre;
   no condition is imposed on its special fibres.
3. Set b(u,v,x) = (uv inverse)x and A = b^*L. Apply `lem-sfb-field-product-square-power`
   over the fraction field to H, H, X and A. Step 2 verifies geometric integrality;
   `lem-pc-proper-base-change`, `lem-weil-pbc-separated-base-change`, and
   `lem-weil-pbc-qcqs-morphism-permanence` preserve the other hypotheses. Obtain r >= 1
   and a generic base line J. Set M = L.tensorPow r. Pullbacks preserve lines, tensors,
   and duals by their local rank-one generator formulas (`def-pc-module-pullback`,
   `def-sc-invertible-module`).
4. On Y form C = c12^*M tensor p^*M tensor (c1^*M) inverse tensor (c2^*M) inverse,
   where c12(g,h,x) = (gh)x, c1(g,h,x) = gx, c2(g,h,x) = hx, and p projects to X.
   Pull the field-product identity back along (g,h,x) maps to (g,e,h inverse,e,x).
   Its four factors evaluate at (gh)x, x, gx, hx, in that order, so C_K = f_K^*N_K
   for f : Y to T. This uses only pullback composition and line cancellation.
5. Descend N_K to T over a basic open of the base using
   `lem-trf-invertible-affine-limit-descent` on the directed system indexed by finite
   subsets of nonzero elements of D. The transition maps are localizations and their
   limit is T_K. Regular local rings of T are UFDs by
   `lem-trf-regular-local-ufd-boundary-factorization` with the empty parameter tuple.
   Then `lem-sfb-invertible-extension-factorial-complement` extends the line to N on T.
6. Put R = C tensor (f^*N) inverse. It is trivial over the generic base fibre. Apply
   `lem-sfb-normal-noetherian-generic-line-pullback` to p : Y to X. The base X is normal
   integral, both schemes are Noetherian, p is smooth and flat, and its fibres are the
   nonempty integral products of two geometric H-fibres from step 2. The generic point
   of X lies over the generic base point, so R is trivial on the generic fibre of p.
   Obtain P on X with R = p^*P.
7. Pull back along sigma(x) = (e,e,x). The unit law trivializes sigma^*C. If e2 = (e,e),
   this gives P = q^*(e2^*N) inverse. Using qp = tf gives C = f^*N0, where
   N0 = N tensor t^*(e2^*N) inverse. Only tensor pullback composition and cancellation
   of invertible modules are used here.
8. For arbitrary B and g,h, pull this identity back along (x,b) maps to (g(b),h(b),x).
   The four left factors are the (gh), identity, g inverse-line, and h inverse-line
   pullbacks of M_B; the right side is q_B^*(g,h)^*N0. Tensor with the two translated
   lines and cancel to obtain the displayed square identity. The same r works for
   every B, including empty, disconnected, or nonreduced schemes. -/
theorem exists_tensorPow_square_of_dedekind_action
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]
    (hdim : ringKrullDim D ≤ 1)
    (H : Over (Spec (CommRingCat.of D))) [GrpObj H]
    [Smooth H.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [GeometricallyConnected H.hom]
    (X : Over (Spec (CommRingCat.of D)))
    [Smooth X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [ModObj H X]
    (hgeneric : GeometricallyConnected (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D))))))
    (L : X.left.Modules) [L.IsInvertible] :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ (B : Over (Spec (CommRingCat.of D))) (g h : B ⟶ H),
      ∃ N : B.left.Modules, N.IsInvertible ∧
        Nonempty
          (((Scheme.Modules.tensorPullback
              (((snd X B ≫ (g * h)) • fst X B).left)).obj (L.tensorPow r) ⊗
            (Scheme.Modules.tensorPullback (fst X B).left).obj (L.tensorPow r)) ≅
           (((Scheme.Modules.tensorPullback
               (((snd X B ≫ g) • fst X B).left)).obj (L.tensorPow r) ⊗
             (Scheme.Modules.tensorPullback
               (((snd X B ≫ h) • fst X B).left)).obj (L.tensorPow r)) ⊗
            (Scheme.Modules.tensorPullback (snd X B).left).obj N)) := by
  sorry

end AlgebraicGeometry
