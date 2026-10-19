/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.JacobsonSpace
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Sheaf.AlgebraicGeometry.EtaleCompletedLocalRingIso

/-! # Étale locality of nodal completed local algebras

Source: Stacks Project, curves.tex, Tag 0C57, lemma-node-etale-local, and section-nodal
(blueprint: lem-trf-nodal-point-etale-locality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical coefficient map into the maximal-ideal completion of a local ring.
It is the composite of constants on `Spec k`, pullback to global sections, the germ map,
and the completion map. No coefficient field or splitting is chosen.
Source: Stacks Project, curves.tex, section-nodal and Tag 0C57
(blueprint: lem-trf-nodal-point-etale-locality). -/
noncomputable def Scheme.Hom.completedLocalScalarMap
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    k →+* AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) :=
  (algebraMap (X.presheaf.stalk x)
    (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x))).comp
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm x).hom)

/-- Nodal completed local `k`-algebras are invariant under an étale map of curves;
either nodal presentation also forces both points to be closed.
Source: Stacks Project, curves.tex, Tag 0C57, lemma-node-etale-local, and section-nodal
(blueprint: lem-trf-nodal-point-etale-locality).

Proof plan:
1. Suppose the completion at `e y` is the nodal `k`-algebra. Its residue field is `k`.
   Local finite type over a field makes the local ring Noetherian. By
   lem-weil-pbc-local-completion-local-ring, completion preserves the residue field,
   so the structure map from `k` to the residue field at `e y` is an isomorphism.
   Apply lem-trf-etale-completed-local-ring-iso: both points are closed, the residue
   field map is an isomorphism, and the completed local map is an isomorphism.
   This map respects constants, so transport the nodal `k`-algebra presentation to `y`.
2. Conversely, suppose the completion at `y` is the nodal `k`-algebra. The composite
   structure map on `D` is locally of finite type, since étale maps are locally of
   finite presentation. Its stalk is Noetherian. The same completion-residue-field
   argument identifies its residue field with `k` as a `k`-algebra. Apply the second
   case of lem-trf-etale-completed-local-ring-iso to obtain closedness of both points
   and the completed local isomorphism. Transport the nodal presentation back to `e y`.
-/
theorem nodalPoint_etale_locality
    {k : Type u} [Field k] [IsAlgClosed k]
    {C D : Scheme.{u}} (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hpure : C.IsPureDimension 1) (e : D ⟶ C) [Etale e] (y : D) :
    (Nonempty
      (@AlgEquiv k
        (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
          (C.presheaf.stalk (e y)))
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
        _ _ _ (f.completedLocalScalarMap (e y)).toAlgebra inferInstance) ↔
      Nonempty
        (@AlgEquiv k
          (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk y)) (D.presheaf.stalk y))
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
          _ _ _ ((e ≫ f).completedLocalScalarMap y).toAlgebra inferInstance)) ∧
    ((Nonempty
      (@AlgEquiv k
        (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
          (C.presheaf.stalk (e y)))
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
        _ _ _ (f.completedLocalScalarMap (e y)).toAlgebra inferInstance) ∨
      Nonempty
        (@AlgEquiv k
          (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk y)) (D.presheaf.stalk y))
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
          _ _ _ ((e ≫ f).completedLocalScalarMap y).toAlgebra inferInstance)) →
      e y ∈ closedPoints C ∧ y ∈ closedPoints D) := by
  sorry

end AlgebraicGeometry
