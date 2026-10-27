/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.QuasiAffine
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.RelativeAmpleAbsoluteTwist
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.AmpleIso

/-! # Ampleness from an orbit cover by affine section opens

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Proposition 6.4(b),
printed p.16 in the March 31, 2026 version, sufficient direction, specialized to a
Noetherian normal domain, smooth schemes, and affine section loci.
(blueprint: lem-sfb-connected-action-orbit-section-ampleness).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.Scheme.Modules

/-- An arbitrary invertible module is absolutely ample if its affine positive-power
section opens meet every orbit of a smooth group with geometrically connected fibres.
The union `V` ranges over all such section opens; the image equality is on underlying
points of the fibre product, not just on rational points of the group.

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Proposition 6.4(b),
printed p.16 in the March 31, 2026 version, sufficient direction in the smooth
Noetherian specialization, with affine rather than quasi-affine section loci.
(blueprint: lem-sfb-connected-action-orbit-section-ampleness).

Proof plan:
1. Spec A is normal integral Noetherian: use the affine stalk localization description
   (lem-weil-pbc-affine-open-stalk-localization). A common denominator in a monic
   equation over A_p shows that A_p is integrally closed. Smooth normal ascent
   (lem-sfb-smooth-normal-ascent) and finite-type Noetherian ascent
   (lem-weil-pbc-finite-type-over-noetherian) give the same properties on each component
   of X. Smoothness gives local finite presentation (lem-pc-smooth-flat); separatedness
   and quasi-compactness give the remaining finite-presentation hypotheses.
2. The finite disjoint integral clopen components of a normal Noetherian scheme
   (rem-pc-regular-normal) are invariant: every orbit map from H over a residue field
   is connected, so its component label is constant and equals that of its unit point.
   Inversion gives a^{-1}(C) = H times C, including after the normal base changes used below.
3. Under an affine base change, the pulled-back section has the inverse-image
   nonvanishing locus (lem-weil-pbc-invertible-pullback-tensor). Affine fibre products
   are affine (lem-weil-pbc-fibre-product-affine-spectra), as are clopen pieces of them
   (lem-weil-pbc-closed-immersion-affine-cover-criterion). Surjectivity survives base
   change (lem-weil-pbc-surjective-base-change), and Step 2 restricts the orbit cover to
   each invariant component. Only pulled-back sections are needed.
4. First suppose Y is integral, has a base section, and has geometrically integral
   generic fibre. By lem-sfb-pointed-generic-integral-action-square-power, some positive
   power M of L satisfies the square condition. Taking the same power of every section
   preserves its locus. Thus lem-sfb-square-action-affine-orbit-criterion makes M ample.
   Its positive-power affine loci are also positive-power affine loci of L, proving
   ampleness of L by def-weil-pbc-ample-invertible-module.
5. For integral Y use strong induction on the finite positive geometric generic
   component count N. The induction ranges over all normal integral Noetherian affine
   bases. By lem-sfb-smooth-self-product-component-rank, W = Y times Y is a finite
   disjoint union of integral clopen C_i. The diagonal lies in C_0, which has a section
   over Y and geometric generic component count one; every other C_i has count less
   than N. No surjectivity of Y onto the original base is needed.
6. The base-changed group acts on the second factor of W. Smoothness, separatedness
   and finite type survive base change (lem-pc-proper-base-change and
   lem-pod-separated-finite-type-base-change). Geometric connectedness follows from
   the field quantifier. Step 2 makes C_i invariant. Above every nonempty affine open
   B in Y, the component-rank lemma preserves integrality and the counts, and Step 3
   preserves the affine section orbit cover.
7. Over B, Step 4 proves ampleness on C_0, and induction proves it on the other C_i.
   Extend witnessing sections by zero across the other clopen pieces. Their loci are
   unchanged and their finite union is quasi-compact. This proves ampleness of the
   second-factor pullback of L on W_B. Empty B gives the vacuous ample condition.
   Hence this pullback is relatively ample for W to Y.
8. The image U of Y in the original base is open by lem-pc-smooth-flat and
   lem-weil-pbc-flat-lfp-open, and is quasi-compact. The induced Y to U is smooth
   (lem-weil-pbc-smooth-restrict-open-subschemes) and surjective. A finite affine cover
   B_j of Y (lem-weil-pbc-qcqs-finite-affine-open-cover) is an fpqc covering of U:
   the maps are flat; affine neighborhoods above each affine open of U have open
   images covering it, and quasi-compactness selects finitely many of them.
9. The base change along B_j is W_{B_j}, with the same second-factor pullback line.
   Step 7 gives relative ampleness there. Apply the scheme case of
   lem-sfb-space-relative-ampleness-fpqc-descent to descend relative ampleness of the
   supplied line L for Y to U. This does not descend an arbitrarily chosen line.
10. The quasi-compact open U in an affine scheme is quasi-affine. Its affine principal
    neighborhoods (lem-sfb-quasiaffine-affine-basic-open-criterion) make O_U ample.
    The map Y to U is quasi-compact by lem-weil-pbc-qcqs-morphism-permanence. Apply
    lem-sfb-relative-ample-absolute-twist with O_U; its pullback twists are the unit.
    By lem-sc-ample-iso this proves absolute ampleness of L, completing the induction.
11. Finally decompose X into its finitely many integral clopen components. Their
    structure maps remain smooth separated of finite type and their orbit covers
    restrict by Steps 2 and 3. Apply the integral case and extend sections by zero
    as in Step 7 to prove ampleness on X. If X is empty, it is quasi-compact and
    the pointwise condition in IsAmple is vacuous.
-/
theorem isAmple_of_connected_action_orbit_section_cover
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (H X : Over (Spec (.of A))) [GrpObj H] [ModObj H X]
    [Smooth H.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (hconnected : ∀ (Ω : Type u) [Field Ω] (s : Spec (.of Ω) ⟶ Spec (.of A)),
      ConnectedSpace (Limits.pullback (C := Scheme.{u}) H.hom s))
    [Smooth X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (L : X.left.Modules) [L.IsInvertible]
    (V : X.left.Opens)
    (hV : V = sSup {U : X.left.Opens | ∃ n : ℕ, 0 < n ∧
      ∃ s : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤),
        IsAffineOpen U ∧ (U : Set X.left) = nonvanishingLocus (L.tensorPow n) s})
    (horbit : (γ[H,X]).left '' ((snd H X).left ⁻¹' (V : Set X.left)) = Set.univ) :
    IsAmple X.left L := by
  sorry

end AlgebraicGeometry.Scheme.Modules
