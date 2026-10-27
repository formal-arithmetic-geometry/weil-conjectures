/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.FibreResidueArrow
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.FieldSpecializationTrdegDrop
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Finite point orbits of an integral descent relation

Source: the agent-formulated finite-orbit prerequisite for Raynaud,
Un critère d'effectivité de descente, Theorem 4.1(ii), pp. 16–21;
Stacks Project, Morphisms, Tags 01WL, 06RU and 01RL.
(blueprint: lem-sfb-integral-descent-finite-point-orbits).

The domain of the relation is literally `V ×_T (T ×_S T)`. Its second map is the
canonical pullback-pasting isomorphism followed by the existing universal transport
`D.toHom`. The conclusion concerns the image of a point-set fibre in `V`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For an integral fpqc morphism with finite underlying fibres, every point orbit of a
locally finitely presented, locally Noetherian scheme with descent datum is finite.
The first relation map is `pullback.fst V.hom (pullback.fst q q)`. The second is the
canonical identification of its domain with `V ×_S T`, followed by `D.toHom`.

Source: agent-formulated finite-orbit prerequisite for Raynaud,
Un critère d'effectivité de descente, Theorem 4.1(ii), pp. 16–21, for an integral fpqc
cover with finite underlying fibres; Stacks Project, Morphisms, Tags 01WL and 06RU.
(blueprint: lem-sfb-integral-descent-finite-point-orbits).

Proof:
1. Write p = V.hom, t₀ = p(v), s = q(t₀). Both projections T ×_S T → T and both
   relation maps are integral, by lem-sbc-integral-morphism-base-change and
   def-weil-finite-integral-morphism; the second map is a projection after the
   isomorphism of def-pd-descent-datum. Their residue-field extensions, and those
   of q, are algebraic by lem-a1-integral-residue-extension-algebraic.
2. For each t above s, put V_t = V ×_T Spec kappa(t). Cancelling the first V factor
   identifies the fibre W of the first relation map over v with Spec kappa(v) ×_S T.
   Its fibre W_t over t is Spec (kappa(v) ⊗_{kappa(s)} kappa(t)), and the second
   relation map induces h_t : W_t → V_t. Its image, viewed in V, is the orbit
   intersected with p⁻¹(t). Use def-pc-scheme-fibre,
   lem-weil-pbc-fibre-product-affine-spectra, def-pc-fibre-product and
   lem-zl-fibre-residue-arrow for these identifications and their residue maps.
3. At z in W_t, with images w in the relation and x in V, both kappa(v) → kappa(w)
   and kappa(x) → kappa(w) are algebraic, and kappa(z) = kappa(w). Algebraic
   extensions have transcendence degree zero by def-kun-transcendence-degree.
   Apply lem-sbc-transcendence-degree-tower to these towers over kappa(s), then
   to kappa(t)/kappa(s). Every point in h_t(W_t) has the same transcendence degree
   over kappa(t), equal to trdeg_{kappa(s)} kappa(v). The structural residue maps
   of lem-zl-fibre-residue-arrow give the required scalar towers.
4. By lem-weil-pbc-qcqs-morphism-permanence, V_t is locally of finite presentation,
   hence locally of finite type over the field kappa(t). It is locally Noetherian
   by pqf-lem-locnoeth-lft. Distinct points of h_t(W_t) cannot specialize to each
   other: lem-sfb-field-specialization-trdeg-drop would strictly decrease the
   common degree of step 3. The affine W_t is quasi-compact by
   lem-weil-pbc-affine-scheme-qcqs, so
   lem-sfb-quasicompact-antichain-image-finite makes its image finite.
5. The defining pullback equality and the fact that the datum is over T ×_S T
   imply that the orbit lies above s. It is the union of its intersections with
   p⁻¹(t) for t in q⁻¹(s). This index set is finite by hypothesis and every
   intersection is finite by step 4. Their union is finite. This only asserts
   finiteness of the image in V, not of the scheme-theoretic fibre of the first map.
-/
theorem integral_descent_finite_point_orbit
    {T S : Scheme.{u}} (q : T ⟶ S)
    [IsIntegralHom q] [Surjective q] [Flat q] [QuasiCompact q]
    (hq : ∀ s : S, (q ⁻¹' {s}).Finite)
    (V : Over T) [LocallyOfFinitePresentation V.hom] [IsLocallyNoetherian V.left]
    (D : Over.DescentDatum q V) (v : V.left) :
    (((pullbackRightPullbackFstIso q q V.hom).hom ≫ D.toHom) ''
      ((pullback.fst V.hom (pullback.fst q q)) ⁻¹' {v})).Finite := by
  sorry

end AlgebraicGeometry
