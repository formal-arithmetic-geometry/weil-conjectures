/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Normalization and reduced boundary of a formally nodal marked curve

Source: Stacks Project, Curves, Tag 0E38, final completion argument; Varieties,
Tag 0C45; Divisors, Tag 01WX; marked integral-curve synthesis in the DAG
(blueprint: lem-trf-completed-curve-boundary-geometry).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

open Classical in
/-- An integral proper marked curve with the indicated smooth and nodal completions has
smooth proper connected normalization. Its nonsmooth locus is exactly the marked nodes;
normalization is an isomorphism over their complement. The reduced inverse image of all
marked points is the sum of its distinct closed points, an effective Cartier divisor.
Its dual ideal is the associated invertible module. The canonical divisor section is an
isomorphism off the boundary, specifying the canonical trivialization there.

The two closed sets encode the disjoint partition of the finite marked set. The scalar
identities make the completed-ring isomorphisms isomorphisms of local k-algebras. Ring
isomorphisms of these local rings preserve their maximal ideals and their adic topologies.
The stalk ideal is expressed as the image of the affine ideal under the germ map.

Source: Stacks Project, Curves, Tag 0E38, final completion argument; Varieties,
Tags 0BXR, 0C45 and 0B8Y; Divisors, Tags 0AG8 and 01WX
(blueprint: lem-trf-completed-curve-boundary-geometry).

Proof:
1. Finite type over a field gives Noetherianity
   (lem-weil-pbc-finite-type-over-noetherian). The one-variable field power-series ring
   is regular (lem-weil-pbc-power-series-field-cohen-regular-complete); completion detects
   regularity (lem-weil-pbc-completion-regular-local), so marked regular stalks are regular.
2. The two coordinate classes in k[[u,v]]/(uv) are nonzero and multiply to zero, as seen
   by evaluating either variable at zero (def-weil-pbc-multivariate-power-series).
   This ring is not regular (lem-sc-regular-local-domain). Completion detects regularity,
   so the marked nodal stalks are not regular.
3. The complement of the nodes is regular: use the preceding regular stalks and smooth
   regularity off all marked points (lem-weil-pbc-smooth-scheme-over-field-regular and
   def-weil-regular-scheme). The field is perfect, so this open is smooth
   (lem-trf-regular-perfect-field-smooth). Nodes cannot be smooth by step 2.
4. Normalization properties (lem-sc-normalization-properties) give finiteness, properness,
   dimension one and smoothness. Integral closures in the common function field are
   domains (def-sc-normalization), so normalization is integral, nonempty and connected,
   and hence is a connected curve (def-sc-curves).
5. Regularity implies normality (rem-pc-regular-normal). Normalization is an isomorphism
   over this normal open (lem-sc-normalization-properties), including all marked regular
   points.
6. Finite fibres give finiteness of the inverse image of the marked set
   (lem-weil-pbc-finite-closed-map-finite-fibres). Its points are closed: they are nongeneric
   points on an integral dimension-one scheme (def-kun-topological-krull-dimension).
7. Sum the distinct closed points once (def-sc-divisor). Each is Cartier
   (lem-sc-point-cartier), so the sum is Cartier. Near each point remove the other marked
   points: its ideal is the maximal ideal; elsewhere it is the unit ideal. These are
   precisely the radical ideals of the reduced inverse image of the marked set.
8. The associated module is the dual ideal (def-pc-divisor-line-bundle). A regular local
   generator of the ideal identifies its dual with the structure module, proving
   invertibility (def-sc-invertible-module). Off the boundary the ideal inclusion is the
   identity of the structure module; its dual section is therefore the canonical unit,
   giving the canonical trivialization, also when the boundary is empty.
-/
theorem completed_curve_boundary_geometry
    (k : Type u) [Field k] [IsAlgClosed k]
    (Z : Scheme.{u}) [IsIntegral Z] (p : Z ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim Z = 1)
    (Sreg Snode : Closeds Z)
    (hfinite : ((Sreg : Set Z) ∪ (Snode : Set Z)).Finite)
    (hclosed : (Sreg : Set Z) ∪ (Snode : Set Z) ⊆ closedPoints Z)
    (hdisjoint : Disjoint Sreg Snode)
    (hsmooth : Smooth (Scheme.Opens.ι (X := Z) (Sreg ⊔ Snode).compl ≫ p))
    (hreg : ∀ s ∈ Sreg,
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Z.presheaf.stalk s))
          (Z.presheaf.stalk s) ≃+* MvPowerSeries (Fin 1) k,
        ∀ a : k, e (AdicCompletion.of (IsLocalRing.maximalIdeal (Z.presheaf.stalk s))
          (Z.presheaf.stalk s) (Z.presheaf.germ ⊤ s (Set.mem_univ s)
            (p.appTop ((Scheme.ΓSpecIso (.of k)).inv a)))) = MvPowerSeries.C a)
    (hnode : ∀ s ∈ Snode,
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Z.presheaf.stalk s))
          (Z.presheaf.stalk s) ≃+*
            (MvPowerSeries (Fin 2) k ⧸ Ideal.span
              {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}),
        ∀ a : k, e (AdicCompletion.of (IsLocalRing.maximalIdeal (Z.presheaf.stalk s))
          (Z.presheaf.stalk s) (Z.presheaf.germ ⊤ s (Set.mem_univ s)
            (p.appTop ((Scheme.ΓSpecIso (.of k)).inv a)))) =
              Ideal.Quotient.mk _ (MvPowerSeries.C a)) :
    IsFinite Z.fromNormalization ∧
    IsIntegral Z.normalization ∧
    IsProper (Z.fromNormalization ≫ p) ∧
    Smooth (Z.fromNormalization ≫ p) ∧
    IsConnectedCurve (Z.fromNormalization ≫ p) ∧
    (∀ z : Z, z ∉ p.smoothLocus ↔ z ∈ Snode) ∧
    IsIso (Z.fromNormalization ∣_ Snode.compl) ∧
    ∃ (E : closedPoints Z.normalization →₀ ℕ) (B : Z.normalization.IdealSheafData),
      (∀ x : closedPoints Z.normalization,
        E x = if Z.fromNormalization x.val ∈ Sreg ⊔ Snode then 1 else 0) ∧
      B = Divisor.idealSheaf E ∧
      B = ((IdealSheafData.vanishingIdeal (Sreg ⊔ Snode)).comap
        Z.fromNormalization).radical ∧
      B.IsInvertible ∧
      (B.support : Set Z.normalization) = Z.fromNormalization ⁻¹' (Sreg ⊔ Snode : Closeds Z) ∧
      (B.support : Set Z.normalization).Finite ∧
      (∀ x ∈ B.support, ∀ (U : Z.normalization.affineOpens) (hx : x ∈ (U : Z.normalization.Opens)),
        Ideal.map (Z.normalization.presheaf.germ U x hx).hom (B.ideal U) =
          IsLocalRing.maximalIdeal (Z.normalization.presheaf.stalk x)) ∧
      (Modules.dual B.toModules).IsInvertible ∧
      IsIso ((SheafOfModules.overFunctor Z.normalization.ringCatSheaf B.support.compl).map
        ((Modules.dual B.toModules).unitHomEquiv.symm
          ((SheafOfModules.homObjSectionsEquiv B.toModules
            (SheafOfModules.unit Z.normalization.ringCatSheaf)).symm B.toModulesι))) := by
  sorry

end AlgebraicGeometry.Scheme
