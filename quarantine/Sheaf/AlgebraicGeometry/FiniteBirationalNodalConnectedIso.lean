/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.AlgebraicGeometry.NodalPointEtaleLocality
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Finite birational maps to nodal curves with connected geometric fibres

Source: Temkin, Stable modification of relative curves, Appendix B, printed pp. 56--57,
ordinary points and their finite modifications; Stacks Project, Morphisms, Tag 0AB1.
(blueprint: lem-trf-finite-birational-nodal-connected-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite surjective map between reduced finite-type pure one-dimensional schemes over
an algebraically closed field is an isomorphism if its target is nodal, it is an isomorphism
above an open meeting every target component, and all its geometric fibres are connected.
Neither scheme is assumed connected, separated or proper. The completed local algebra uses
the canonical scalar map, and nodality is required only at nonsmooth closed points.

Source: Temkin, Stable modification of relative curves, Appendix B, printed pp. 56--57,
ordinary-point characterization and normalization description; Stacks Project, Tag 0AB1.
(blueprint: lem-trf-finite-birational-nodal-connected-iso).

Proof plan:
1. By lem-weil-pbc-finite-type-over-noetherian both schemes are Noetherian, and
   lem-weil-pbc-noetherian-finitely-many-components makes their component sets finite.
   A source component cannot map into a finite fibre, since its dimension is one.
   Its generic point therefore maps to a target generic point, which belongs to the
   specified open. The isomorphism there identifies components and their function fields.
2. Reducedness and density embed the target structure sheaf in the finite source algebra.
   Embed the latter componentwise in the common function fields and then in their integral
   closures, using lem-weil-pbc-finite-algebra-is-integral and def-sc-normalization.
   Apply lem-sc-normalization-properties. On affine opens of the smooth locus meeting just
   one component, lem-sc-smooth-normal and lem-trf-finite-birational-normal-iso show that
   the original finite map is an isomorphism. The possible discrepancy is at nodes only.
3. At a node write R for the target stalk, A for the finite source algebra stalk, and B for
   the component-normalization algebra stalk. The node case of
   lem-trf-ordinary-point-delta-branches gives two branches and dim_k(B/R) = 1.
   The inclusions R ⊆ A ⊆ B imply A = R or A = B.
4. If A = B, the fibre has the two distinct normalization points. A finite scheme over k
   with two points is disconnected, contradicting connectedness of the geometric fibre.
   Thus A = R at every node.
5. The structure-sheaf map is now an isomorphism at all stalks. Since a finite map is affine,
   its ring maps on an affine target cover are isomorphisms; these identify the map globally.
-/
theorem isIso_of_finite_birational_nodal_connected
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsReduced X] [IsReduced Y]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (hXdim : X.IsPureDimension 1) (hYdim : Y.IsPureDimension 1)
    (hnodal : ∀ y : Y, y ∈ closedPoints Y → y ∉ (Y ↘ Spec (.of k)).smoothLocus →
      Nonempty
        (@AlgEquiv k
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
          _ _ _ ((Y ↘ Spec (.of k)).completedLocalScalarMap y).toAlgebra inferInstance))
    (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (U : Y.Opens)
    (hmeets : ∀ Z : Set Y, Z ∈ irreducibleComponents Y → (Z ∩ (U : Set Y)).Nonempty)
    (hUiso : IsIso (f ∣_ U))
    (hconnected : ∀ y : Y,
      ConnectedSpace ↥(pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y))) :
    IsIso f := by
  sorry

end AlgebraicGeometry
